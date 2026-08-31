/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Grammar
public import Strata.Languages.Core.Verifier
public import Strata.DL.Imperative.MetaData
public import Strata.Pipeline.Messages
import StrataDDM.AST

namespace Strata
namespace RelRL

public section

open StrataDDM (Operation Arg QualifiedIdent)

/-! # RelRL to Core translation

A `biproc` becomes a Core procedure by self-composition: the left side keeps its
source names, every right-side name is primed, and the two are concatenated so a
relational formula is an ordinary Core `assert` over both. The prime is what
separates the two programs in the one Core scope they now share, so it holds for
asymmetric names too — `Var | u : int ;` declares the right program's `u`, which
is `u'` in Core.

Lowering runs inside Core's `TransM`, threading its `TransBindings` from one
side to the next. **That threading mirrors the `@[scope(…)]` chain in
`Grammar.lean` and must be kept in step with it** — see CLAUDE.md, "The other
invariant". `docs/workflows/pipeline.md` walks the stages; `docs/design.md`
argues the choices. -/

structure TranslateState where
  diagnostics : Array Message := #[]

abbrev TranslateM := StateM TranslateState

def TranslateM.run (m : TranslateM α) : α × Array Message :=
  let (v, s) := StateT.run m {}
  (v, s.diagnostics)

def emit_diagnostic (d : Message) : TranslateM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics.push d }

/-- Report a broken translator invariant. `Grammar.lean` fixes every argument
shape matched below, so a fallback branch firing means the two have drifted —
a bug here, not in the user's program. `.strataBug` makes it exit 3. -/
def emit_invariant_violation (msg : String) : TranslateM Unit :=
  emit_diagnostic (Message.fromString s!"translator invariant violated: {msg}" .strataBug)

/-! ## Priming

A right-hand fragment is renamed apart before the two sides are concatenated.
Both helpers fold Core's own substitution, so no traversal is written here.

**What gets primed is every program variable the fragment mentions.** Core has
no top-level variables — a constant is a 0-ary function, so it lowers to `.op`
and never to `.fvar` — which is what makes that safe: the only names these
helpers can reach are the two programs' own locals, and on the right side every
one of them belongs to the right program. Renaming against a list of *expected*
names instead would let anything off that list fall through to the left
program's variable; `docs/issues.md` records what that cost. -/

/-- Top-level declared names. One nested in an `if`/`while` body stays
block-scoped, so it cannot collide across sides. Used for the collision check,
not for priming. -/
def top_level_declared (stmts : List Core.Statement) : List String :=
  stmts.filterMap fun
    | .init lhs _ _ _ => some lhs.name
    | _ => none

/-- Every program variable a statement fragment mentions — declared, assigned
or read, at any depth. -/
def fragment_names (stmts : List Core.Statement) : List String :=
  let ids := Imperative.HasVarsImp.definedVars (P := Core.Expression) stmts false
    ++ Imperative.HasVarsImp.modifiedVars (P := Core.Expression) stmts
    ++ Imperative.HasVarsImp.readVars (P := Core.Expression) stmts
  (ids.map (·.name)).eraseDups

/-- The same, for an expression. -/
def expr_names (e : Core.Expression.Expr) : List String :=
  ((Imperative.HasFvars.getFvars (P := Core.Expression) e).map (·.name)).eraseDups

/-- Renaming is a *sequential* fold over Core's own substitution, so a name
whose primed form is also in the list would be primed twice — `{n, n'}` sends
`n` to `n''` if `n` goes first. Longest first makes that impossible: `x'` is
always longer than `x`, so it is already renamed when `x` produces one. -/
def longest_first (names : List String) : List String :=
  names.mergeSort (fun a b => b.length ≤ a.length)

def prime_stmts (names : List String) (stmts : List Core.Statement) : List Core.Statement :=
  (longest_first names).foldl (init := stmts) fun ss v =>
    let v' : Core.CoreIdent := ⟨v ++ "'", ()⟩
    Core.Block.renameLhs (Core.Block.substFvar ss ⟨v, ()⟩ (.fvar () v' none)) ⟨v, ()⟩ v'

def prime_expr (names : List String) (e : Core.Expression.Expr) : Core.Expression.Expr :=
  (longest_first names).foldl (init := e) fun acc v =>
    Lambda.LExpr.substFvar acc ⟨v, ()⟩ (.fvar () ⟨v ++ "'", ()⟩ none)

/-! ## Lowering -/

/-- Lower one side's statements. The synthetic `Core.block` wrap is all
`translateBlock` needs; `bindings` is the scope the side was elaborated in. -/
def lower_side (p : StrataDDM.Program) (bindings : TransBindings) (arg : Arg) :
    TransM (List Core.Statement × TransBindings) := do
  match arg with
  | .seq ann _ stmts =>
    translateBlock p bindings
      (.op { ann, name := q`Core.block, args := #[.seq ann .newline stmts] })
  | _ => TransM.error "bicommand side is not a statement sequence"

/-- Apply one of Core's boolean operators. A relational formula has no Core
surface syntax to route through `translateFnTable`, so it builds the same
applications directly. -/
def bool_app (op : Core.Expression.Expr) (args : List Core.Expression.Expr) :
    Core.Expression.Expr :=
  Lambda.LExpr.mkApp () op args

/-- Lower a `Var` side's `DeclList`, by putting it back in the
`Core.varStatement` Core's grammar wraps it in. Nothing is initialized. -/
def lower_decl_list (p : StrataDDM.Program) (bindings : TransBindings) (dl : Arg) :
    TransM (List Core.Statement × TransBindings) := do
  let ann := dl.ann
  let stmt : Arg := .op { ann, name := q`Core.varStatement, args := #[.option ann none, dl] }
  translateBlock p bindings
    (.op { ann, name := q`Core.block, args := #[.seq ann .newline #[stmt]] })

/-- Lower a relational formula to one Core `bool` expression. `Grammar.lean`
lists what each form means; here, "the right state" is just the primed reading —
a right-hand fragment has every variable it mentions renamed. -/
partial def lower_rformula (p : StrataDDM.Program) (bindings : TransBindings)
    (arg : Arg) : TransM Core.Expression.Expr := do
  match arg with
  | .op op =>
    match op.name, op.args with
    | q`RelRL.rf_agree, #[.ident _ x] =>
      return .eq () (.fvar () ⟨x, ()⟩ none) (.fvar () ⟨x ++ "'", ()⟩ none)
    | q`RelRL.rf_left, #[e] =>
      translateExpr p bindings e
    | q`RelRL.rf_right, #[e] =>
      let e ← translateExpr p bindings e
      return prime_expr (expr_names e) e
    | q`RelRL.rf_both, #[e] =>
      let e ← translateExpr p bindings e
      return bool_app Core.boolAndOp [e, prime_expr (expr_names e) e]
    | q`RelRL.rf_biequal, #[_, l, r] =>
      let l ← translateExpr p bindings l
      let r ← translateExpr p bindings r
      return .eq () l (prime_expr (expr_names r) r)
    | q`RelRL.rf_group, #[r] =>
      lower_rformula p bindings r
    | q`RelRL.rf_not, #[r] =>
      return bool_app Core.boolNotOp [← lower_rformula p bindings r]
    | q`RelRL.rf_and, #[l, r] =>
      return bool_app Core.boolAndOp
        [← lower_rformula p bindings l, ← lower_rformula p bindings r]
    | q`RelRL.rf_or, #[l, r] =>
      return bool_app Core.boolOrOp
        [← lower_rformula p bindings l, ← lower_rformula p bindings r]
    | q`RelRL.rf_implies, #[l, r] =>
      return bool_app Core.boolImpliesOp
        [← lower_rformula p bindings l, ← lower_rformula p bindings r]
    | q`RelRL.rf_iff, #[l, r] =>
      return bool_app Core.boolEquivOp
        [← lower_rformula p bindings l, ← lower_rformula p bindings r]
    | n, args =>
      TransM.error s!"unexpected relational formula {n.fullName} with {args.size} arguments"
  | _ => TransM.error "relational formula is not an operation"

/-- Peel a formula's top-level `/\` so each conjunct becomes its own proof
obligation. `{ … }` is transparent to this; every other connective is opaque,
since its parts are not separately provable. -/
partial def top_conjuncts (arg : Arg) : List Arg :=
  match arg with
  | .op op =>
    match op.name, op.args with
    | q`RelRL.rf_and, #[l, r] => top_conjuncts l ++ top_conjuncts r
    | q`RelRL.rf_group, #[r] => top_conjuncts r
    | _, _ => [arg]
  | _ => [arg]

/-- Which program a projection keeps. -/
inductive Side where
  | left
  | right
  deriving DecidableEq, Repr

def Side.of_string? : String → Option Side
  | "left" => some .left
  | "right" => some .right
  | _ => none

def Side.name : Side → String
  | .left => "left"
  | .right => "right"

/-- The Core name a source name takes on `side`. Self-composition fuses both
programs into one Core scope, so this is the name that must be unique. -/
def Side.core_name : Side → String → String
  | .left, x => x
  | .right, x => x ++ "'"

/-- A name already standing in the fused block: what it collides *as*, plus
enough of where it came from for the message to say so. -/
structure DeclName where
  core : String
  source : String
  side : Side

/-- `verify` fuses the two sides by self-composition; `project` keeps one of them
as a unary program, unprimed and stripped of relational formulas
(`docs/workflows/project.md`). -/
inductive Mode where
  | verify
  | project (side : Side)
  deriving Repr

/-- What a `biproc` body accumulates. `lefts`/`rights` are not yet flushed: an
`Assert` must observe both sides of every bicommand before it, so they are
emitted — lefts, then rights — at each one and again at the end. -/
structure BodyState where
  bindings : TransBindings
  lefts : Array (List Core.Statement) := #[]
  rights : Array (List Core.Statement) := #[]
  out : Array Core.Statement := #[]
  asserts : Nat := 0
  /-- Everything declared into the fused block so far, newest first. -/
  declared : List DeclName := []
  /-- Errors in the source program, located. Distinct from `TransM.error`,
  which reports a broken translator invariant and exits 3. -/
  diagnostics : Array Message := #[]

/-- `TransM.error` needs a fallback value; `TransBindings` has all-default
fields, so an empty accumulator is the natural one. -/
instance : Inhabited BodyState := ⟨{ bindings := {} }⟩

def collision_message (name : String) (side : Side) (core : String) (prev : DeclName) : String :=
  if prev.source == name && prev.side == side then
    s!"`{name}` is declared twice in the {side.name} program"
  else
    s!"`{name}` in the {side.name} program collides with `{prev.source}` in the \
       {prev.side.name} program: self-composition names both `{core}`"

/-- Record `names` as declared on `side`, reporting any the fused block already
holds. Only `.verify` fuses; a projection is one unary program, which Core
checks on its own. -/
def BodyState.declare (s : BodyState) (fr : FileRange) (side : Side)
    (names : List String) : BodyState :=
  names.foldl (init := s) fun s name =>
    let core := side.core_name name
    match s.declared.find? (·.core == core) with
    | some prev =>
      { s with diagnostics := s.diagnostics.push <|
          Message.withRange fr (collision_message name side core prev) .userError }
    | none => { s with declared := ⟨core, name, side⟩ :: s.declared }

def BodyState.flush (s : BodyState) : BodyState :=
  { s with
    out := s.out ++ s.lefts.toList.flatten.toArray ++ s.rights.toList.flatten.toArray
    lefts := #[], rights := #[] }

/-- Lower one bicommand, extending the accumulator. Each branch's binding
threading mirrors that form's `@[scope(…)]` in `Grammar.lean`. Under `project`,
one side is kept verbatim and nothing is primed or checked for collisions —
there is only one program, and Core checks it directly. -/
def lower_bicommand (mode : Mode) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (s : BodyState) (arg : Arg) : TransM BodyState := do
  match arg with
  | .op op =>
    let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) op.ann
    -- Each side's own range, so a collision points at the declaration.
    let src (a : Arg) : FileRange := { file := .file ictx.fileName, range := a.ann }
    match op.name, op.args with
    | q`RelRL.bi_var, #[l, r] =>
      let (ls, b) ← lower_decl_list p s.bindings l
      let (rs, b) ← lower_decl_list p b r
      let rnames := top_level_declared rs
      match mode with
      | .verify =>
        let s := (s.declare (src l) .left (top_level_declared ls)).declare (src r) .right rnames
        return { s with
                 bindings := b
                 lefts := s.lefts.push ls
                 rights := s.rights.push (prime_stmts (fragment_names rs) rs) }
      | .project .left => return { s with bindings := b, lefts := s.lefts.push ls }
      | .project .right => return { s with bindings := b, lefts := s.lefts.push rs }
    | q`RelRL.bi_var_left, #[l] =>
      let (ls, b) ← lower_decl_list p s.bindings l
      match mode with
      | .project .right => return { s with bindings := b }
      | .project .left => return { s with bindings := b, lefts := s.lefts.push ls }
      | .verify =>
        let s := s.declare (src l) .left (top_level_declared ls)
        return { s with bindings := b, lefts := s.lefts.push ls }
    | q`RelRL.bi_var_right, #[r] =>
      let (rs, b) ← lower_decl_list p s.bindings r
      let rnames := top_level_declared rs
      match mode with
      | .verify =>
        let s := s.declare (src r) .right rnames
        return { s with
                 bindings := b
                 rights := s.rights.push (prime_stmts (fragment_names rs) rs) }
      | .project .right => return { s with bindings := b, lefts := s.lefts.push rs }
      | .project .left => return { s with bindings := b }
    | q`RelRL.bi_sync, #[c] =>
      -- One statement; `lower_side` takes the sequence a split's side is.
      let (stmts, bindings) ← lower_side p s.bindings (.seq c.ann .newline #[c])
      let names := top_level_declared stmts
      match mode with
      | .verify =>
        -- One source name, declared into both programs.
        let s := (s.declare (src c) .left names).declare (src c) .right names
        return { s with
                 bindings := bindings
                 lefts := s.lefts.push stmts
                 rights := s.rights.push (prime_stmts (fragment_names stmts) stmts) }
      | .project _ =>
        return { s with bindings := bindings, lefts := s.lefts.push stmts }
    | q`RelRL.bi_embed, #[l, r] =>
      match mode with
      | .verify =>
        let (ls, _) ← lower_side p s.bindings l
        let (rs, _) ← lower_side p s.bindings r
        -- A split's declarations stay local to their side, but they land in the
        -- one fused block, so they still have to be unique in it.
        let s := (s.declare (src l) .left (top_level_declared ls)).declare
                   (src r) .right (top_level_declared rs)
        return { s with
                 lefts := s.lefts.push ls
                 rights := s.rights.push (prime_stmts (fragment_names rs) rs) }
      | .project .left =>
        let (ls, _) ← lower_side p s.bindings l
        return { s with lefts := s.lefts.push ls }
      | .project .right =>
        let (rs, _) ← lower_side p s.bindings r
        return { s with lefts := s.lefts.push rs }
    | q`RelRL.bi_assert, #[r] =>
      match mode with
      | .project _ => return s
      | .verify =>
        let s := s.flush
        let mut out := s.out
        let mut i := 0
        for conjunct in top_conjuncts r do
          i := i + 1
          let e ← lower_rformula p s.bindings conjunct
          out := out.push (.assert s!"assert_{s.asserts + 1}_{i}" e md)
        return { s with out := out, asserts := s.asserts + 1 }
    | n, args =>
      TransM.error s!"unexpected bicommand {n.fullName} with {args.size} arguments"
  | _ => TransM.error "biproc body element is not an operation"

/-- Spec clauses to Core statements — `assume` for `requires`, `assert` for
`ensures` — one per top-level conjunct. A projection drops both. -/
def lower_spec_clauses (mode : Mode) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (bindings : TransBindings)
    (kind : String) (assumed : Bool) (arg : Arg) : TransM (Array Core.Statement) := do
  match mode, arg with
  | .project _, _ => return #[]
  | _, .seq _ _ clauses =>
    let mut out : Array Core.Statement := #[]
    let mut n := 0
    for clause in clauses do
      match clause with
      | .op op =>
        let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) op.ann
        match op.args with
        | #[r] =>
          for conjunct in top_conjuncts r do
            n := n + 1
            let e ← lower_rformula p bindings conjunct
            out := out.push <|
              if assumed then .assume s!"{kind}_{n}" e md else .assert s!"{kind}_{n}" e md
        | _ => TransM.error s!"{kind} clause does not hold exactly one relational formula"
      | _ => TransM.error s!"{kind} clause is not an operation"
    return out
  | _, _ => TransM.error s!"biproc's {kind} argument is not a sequence"

/-- `requires` assumptions, then the bicommands, then the `ensures` obligations.
`requires` is lowered against the *incoming* bindings, matching its lack of
`@[scope(…)]`; `ensures` against what the body ends with. -/
def lower_biproc (mode : Mode) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (top : TransBindings)
    (reqs : Arg) (body : Arg) (ens : Arg) :
    TransM (List Core.Statement × Array Message) := do
  match body with
  | .seq _ _ bicommands =>
    let pre ← lower_spec_clauses mode p ictx top "requires" true reqs
    let mut st : BodyState := { bindings := top }
    for bicommand in bicommands do
      st ← lower_bicommand mode p ictx st bicommand
    let done := st.flush
    let post ← lower_spec_clauses mode p ictx done.bindings "ensures" false ens
    return ((pre ++ done.out ++ post).toList, done.diagnostics)
  | _ => TransM.error "biproc body is not a sequence of bicommands"

/-- Commands that add more than one `freeVars` entry per decl they return, and
so break the index alignment `translate_program_with` depends on. Names what was
found, for the message. `docs/issues.md`, "A `datatype` silently misresolves
every later top-level reference" — delete this once that is fixed upstream. -/
def misaligning_command? (op : Operation) : Option String :=
  match op.name, op.args with
  | q`Core.command_datatypes, _ => some "a `datatype` declaration"
  | q`Core.command_recfndefs, #[_, .seq _ _ fns] =>
    if fns.size > 1 then some s!"a `rec` block of {fns.size} functions" else none
  | _, _ => none

/-- Each `RelRL.biproc` becomes a Core procedure of the same name; every other
top-level command is Core syntax, delegated unchanged.

The Core commands go through **one** pass, not one at a time: a `.fvar i`
indexes the program's top-level declarations, so per-command translation
silently resolved every cross-reference to declaration 0. `docs/design.md` has
what that cost. A `biproc` declares no top-level name, so filtering the
bicommands out keeps the indices aligned. -/
def translate_program_with (mode : Mode) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext := Inhabited.default) : TranslateM Core.Program := do
  let coreCommands := p.commands.filter (fun op => op.name != q`RelRL.biproc)
  let coreProgram := StrataDDM.Program.create Core_map "Core" coreCommands
  let (coreDecls, coreErrors) :=
    TransM.run ictx (translateCoreDecls coreProgram {}) p.globalContext
  for e in coreErrors do
    emit_diagnostic (Message.fromString e .strataBug)
  -- WRONG, and unsound: `translateCoreDecls` returns one decl per *command*,
  -- but `command_datatypes` and a multi-function `command_recfndefs` add more
  -- than one `freeVars` entry, so this array is shorter than the index space a
  -- `.fvar i` in a body is resolved against. `docs/issues.md`, "A `datatype`
  -- silently misresolves every later top-level reference".
  let top : TransBindings := { freeVars := coreDecls.toArray }
  -- Refuse the combination rather than lower a body against a `top` that is
  -- known to be short: the misresolution is silent, and can verify a false spec.
  -- Lowering one anyway would trip Core's own `assert!` and bury this message
  -- under its backtraces, so no body is lowered once this fires.
  let misaligning :=
    if p.commands.any (fun op => op.name == q`RelRL.biproc) then
      p.commands.filterMap fun op => (misaligning_command? op).map (fun what => (op, what))
    else #[]
  for (op, what) in misaligning do
    emit_diagnostic <| Message.withRange
      { file := .file ictx.fileName, range := op.ann }
      s!"{what} cannot appear in a file that also declares a `biproc`: \
         references to top-level declarations inside the biproc would silently \
         resolve to the wrong one. docs/issues.md has the mechanism."
      .userError
  let mut procs : List (List Core.Decl) := []
  for op in p.commands do
    if misaligning.isEmpty && op.name == q`RelRL.biproc then
      match op.args with
      | #[.ident _ name, reqs, body, ens] =>
        let ((stmts, sourceErrors), errors) :=
          TransM.run ictx (lower_biproc mode p ictx top reqs body ens) p.globalContext
        for d in sourceErrors do
          emit_diagnostic d
        for e in errors do
          emit_diagnostic (Message.fromString e .strataBug)
        let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) op.ann
        -- The block label says which reading of the bicommand this is.
        let label := match mode with
          | .verify => "biproc"
          | .project side => side.name
        let block : Core.Statement := .block label stmts md
        procs := [.proc
          { header := { name := name, typeArgs := [], inputs := [], outputs := [] },
            spec := { preconditions := [], postconditions := [] },
            body := .structured [block] } md] :: procs
      | _ =>
        emit_invariant_violation "biproc does not have exactly four arguments"
  return { decls := coreDecls ++ procs.reverse.flatten }

/-- Fuse both sides by self-composition — what `verify` and `toCore` translate. -/
def translate_program (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext := Inhabited.default) : TranslateM Core.Program :=
  translate_program_with .verify p ictx

/-- Keep one side as an ordinary unary Core program — what `project` prints. -/
def project_program (side : Side) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext := Inhabited.default) : TranslateM Core.Program :=
  translate_program_with (.project side) p ictx

end
end RelRL
end Strata
