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
source names, the right side's copies are primed, and the two are concatenated
so a relational formula is an ordinary Core `assert` over both.

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

A shared name has to be renamed apart before the two sides are concatenated.
Both helpers fold Core's own substitution, so no traversal is written here. -/

/-- Top-level declared names. One nested in an `if`/`while` body stays
block-scoped, so it can neither collide across sides nor be named by a
formula. -/
def top_level_declared (stmts : List Core.Statement) : List String :=
  stmts.filterMap fun
    | .init lhs _ _ _ => some lhs.name
    | _ => none

def prime_stmts (names : List String) (stmts : List Core.Statement) : List Core.Statement :=
  names.foldl (init := stmts) fun ss v =>
    let v' : Core.CoreIdent := ⟨v ++ "'", ()⟩
    Core.Block.renameLhs (Core.Block.substFvar ss ⟨v, ()⟩ (.fvar () v' none)) ⟨v, ()⟩ v'

def prime_expr (names : List String) (e : Core.Expression.Expr) : Core.Expression.Expr :=
  names.foldl (init := e) fun acc v =>
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
a right-hand fragment has every bi-local it mentions renamed. -/
partial def lower_rformula (p : StrataDDM.Program) (bindings : TransBindings)
    (bilocals : List String) (arg : Arg) : TransM Core.Expression.Expr := do
  match arg with
  | .op op =>
    match op.name, op.args with
    | q`RelRL.rf_agree, #[.ident _ x] =>
      return .eq () (.fvar () ⟨x, ()⟩ none) (.fvar () ⟨x ++ "'", ()⟩ none)
    | q`RelRL.rf_left, #[e] =>
      translateExpr p bindings e
    | q`RelRL.rf_right, #[e] =>
      return prime_expr bilocals (← translateExpr p bindings e)
    | q`RelRL.rf_both, #[e] =>
      let e ← translateExpr p bindings e
      return bool_app Core.boolAndOp [e, prime_expr bilocals e]
    | q`RelRL.rf_biequal, #[_, l, r] =>
      let l ← translateExpr p bindings l
      let r ← translateExpr p bindings r
      return .eq () l (prime_expr bilocals r)
    | q`RelRL.rf_group, #[r] =>
      lower_rformula p bindings bilocals r
    | q`RelRL.rf_not, #[r] =>
      return bool_app Core.boolNotOp [← lower_rformula p bindings bilocals r]
    | q`RelRL.rf_and, #[l, r] =>
      return bool_app Core.boolAndOp
        [← lower_rformula p bindings bilocals l, ← lower_rformula p bindings bilocals r]
    | q`RelRL.rf_or, #[l, r] =>
      return bool_app Core.boolOrOp
        [← lower_rformula p bindings bilocals l, ← lower_rformula p bindings bilocals r]
    | q`RelRL.rf_implies, #[l, r] =>
      return bool_app Core.boolImpliesOp
        [← lower_rformula p bindings bilocals l, ← lower_rformula p bindings bilocals r]
    | q`RelRL.rf_iff, #[l, r] =>
      return bool_app Core.boolEquivOp
        [← lower_rformula p bindings bilocals l, ← lower_rformula p bindings bilocals r]
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
  bilocals : List String := []
  lefts : Array (List Core.Statement) := #[]
  rights : Array (List Core.Statement) := #[]
  out : Array Core.Statement := #[]
  asserts : Nat := 0

/-- `TransM.error` needs a fallback value; `TransBindings` has all-default
fields, so an empty accumulator is the natural one. -/
instance : Inhabited BodyState := ⟨{ bindings := {} }⟩

def BodyState.flush (s : BodyState) : BodyState :=
  { s with
    out := s.out ++ s.lefts.toList.flatten.toArray ++ s.rights.toList.flatten.toArray
    lefts := #[], rights := #[] }

/-- Lower one bicommand, extending the accumulator. Each branch's binding
threading mirrors that form's `@[scope(…)]` in `Grammar.lean`. Under `project`,
one side is kept verbatim and nothing is primed. -/
def lower_bicommand (mode : Mode) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (s : BodyState) (arg : Arg) : TransM BodyState := do
  match arg with
  | .op op =>
    let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) op.ann
    match op.name, op.args with
    | q`RelRL.bi_var, #[l, r] =>
      -- Distinct names, so neither side is primed.
      let (ls, b) ← lower_decl_list p s.bindings l
      let (rs, b) ← lower_decl_list p b r
      match mode with
      | .verify =>
        let s := { s with bindings := b, lefts := s.lefts.push ls }
        return { s with rights := s.rights.push rs }
      | .project .left => return { s with bindings := b, lefts := s.lefts.push ls }
      | .project .right => return { s with bindings := b, lefts := s.lefts.push rs }
    | q`RelRL.bi_var_left, #[l] =>
      let (ls, b) ← lower_decl_list p s.bindings l
      match mode with
      | .project .right => return { s with bindings := b }
      | _ => return { s with bindings := b, lefts := s.lefts.push ls }
    | q`RelRL.bi_var_right, #[r] =>
      let (rs, b) ← lower_decl_list p s.bindings r
      match mode with
      | .verify => return { s with bindings := b, rights := s.rights.push rs }
      | .project .right => return { s with bindings := b, lefts := s.lefts.push rs }
      | .project .left => return { s with bindings := b }
    | q`RelRL.bi_sync, #[c] =>
      -- One statement; `lower_side` takes the sequence a split's side is.
      let (stmts, bindings) ← lower_side p s.bindings (.seq c.ann .newline #[c])
      let bilocals := top_level_declared stmts ++ s.bilocals
      let s := { s with bindings := bindings, bilocals := bilocals, lefts := s.lefts.push stmts }
      match mode with
      | .verify => return { s with rights := s.rights.push (prime_stmts bilocals stmts) }
      | .project _ => return s
    | q`RelRL.bi_embed, #[l, r] =>
      match mode with
      | .verify =>
        let (ls, _) ← lower_side p s.bindings l
        let (rs, _) ← lower_side p s.bindings r
        let rs := prime_stmts (top_level_declared rs ++ s.bilocals) rs
        return { s with lefts := s.lefts.push ls, rights := s.rights.push rs }
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
          let e ← lower_rformula p s.bindings s.bilocals conjunct
          out := out.push (.assert s!"assert_{s.asserts + 1}_{i}" e md)
        return { s with out := out, asserts := s.asserts + 1 }
    | n, args =>
      TransM.error s!"unexpected bicommand {n.fullName} with {args.size} arguments"
  | _ => TransM.error "biproc body element is not an operation"

/-- Spec clauses to Core statements — `assume` for `requires`, `assert` for
`ensures` — one per top-level conjunct. A projection drops both. -/
def lower_spec_clauses (mode : Mode) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (bindings : TransBindings) (bilocals : List String)
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
            let e ← lower_rformula p bindings bilocals conjunct
            out := out.push <|
              if assumed then .assume s!"{kind}_{n}" e md else .assert s!"{kind}_{n}" e md
        | _ => TransM.error s!"{kind} clause does not hold exactly one relational formula"
      | _ => TransM.error s!"{kind} clause is not an operation"
    return out
  | _, _ => TransM.error s!"biproc's {kind} argument is not a sequence"

/-- `requires` assumptions, then the bicommands, then the `ensures` obligations.
`requires` is lowered against the *incoming* bindings and no bi-locals, matching
its lack of `@[scope(…)]`; `ensures` against what the body ends with. -/
def lower_biproc (mode : Mode) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (top : TransBindings)
    (reqs : Arg) (body : Arg) (ens : Arg) : TransM (List Core.Statement) := do
  match body with
  | .seq _ _ bicommands =>
    let pre ← lower_spec_clauses mode p ictx top [] "requires" true reqs
    let mut st : BodyState := { bindings := top }
    for bicommand in bicommands do
      st ← lower_bicommand mode p ictx st bicommand
    let done := st.flush
    let post ← lower_spec_clauses mode p ictx done.bindings done.bilocals "ensures" false ens
    return (pre ++ done.out ++ post).toList
  | _ => TransM.error "biproc body is not a sequence of bicommands"

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
  -- Every branch of `translateCoreDecls` pushes the decl it produced onto
  -- `freeVars`, so the decls it returns *are* that array.
  let top : TransBindings := { freeVars := coreDecls.toArray }
  let mut procs : List (List Core.Decl) := []
  for op in p.commands do
    if op.name == q`RelRL.biproc then
      match op.args with
      | #[.ident _ name, reqs, body, ens] =>
        let (stmts, errors) :=
          TransM.run ictx (lower_biproc mode p ictx top reqs body ens) p.globalContext
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
