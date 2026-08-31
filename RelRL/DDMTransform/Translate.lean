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

A `biproc` becomes a Core procedure holding both programs at once: the left side
keeps its source names, every right-side name is primed, and a relational formula
is then an ordinary Core `assert` over both. The prime is what separates the two
programs in the one Core scope they now share, so it holds for asymmetric names
too — `Var | u : int ;` declares the right program's `u`, which is `u'` in Core.

**The two are interleaved per bicommand, not concatenated.** `(l₁|r₁); (l₂|r₂)`
becomes `l₁; r₁; l₂; r₂` — WhyRel's `Bisplit` emits its left then its right and
`Biseq` composes those, so this follows it. Whole-left-then-whole-right would be
self-composition in the textbook sense, but it is a *different program*: an
`assume` in one side would move across the other side's statements, and could
discharge an obligation the other program raised at an earlier step.
`docs/design.md` has the case.

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

/-- What a `biproc` body accumulates. One output stream: each bicommand emits
its left program's statements and then its right program's, immediately. -/
structure BodyState where
  bindings : TransBindings
  out : Array Core.Statement := #[]
  asserts : Nat := 0
  assumes : Nat := 0
  /-- Everything declared into the fused block so far, newest first. -/
  declared : List DeclName := []
  /-- Errors in the source program, located. Distinct from `TransM.error`,
  which reports a broken translator invariant and exits 3. -/
  diagnostics : Array Message := #[]

/-- `TransM.error` needs a fallback value; `TransBindings` has all-default
fields, so an empty accumulator is the natural one. The `TransBindings` instance
is for the same reason — Core does not declare one, and `lower_params` returns a
tuple containing it. -/
instance : Inhabited TransBindings := ⟨{}⟩
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

/-- Report any name `stmts` mentions that `side` has nothing declared for. The
fragment's own declarations count. `declared` also holds split locals from
earlier bicommands, which are block-scoped by then — so this under-reports
rather than over-reports, which is the safe direction for a check whose job is
to replace a Core error with a better one. -/
def BodyState.check_side (s : BodyState) (fr : FileRange) (side : Side)
    (stmts : List Core.Statement) : BodyState :=
  let own := (Imperative.HasVarsImp.definedVars (P := Core.Expression) stmts false).map (·.name)
  let declared := s.declared.filterMap fun d => if d.side == side then some d.source else none
  (fragment_names stmts).foldl (init := s) fun s name =>
    if own.contains name || declared.contains name then s
    else
      { s with diagnostics := s.diagnostics.push <|
          Message.withRange fr s!"the {side.name} program has no `{name}`" .userError }

/-- The same for a lowered formula, which names both programs at once and so is
checked against Core names — a left declaration under its source name, a right
one under its prime. This is also what catches `Agree x` for an `x` neither
program declares, since that form is built lexically. -/
def check_formula (declared : List DeclName) (fr : FileRange)
    (e : Core.Expression.Expr) : Array Message :=
  (expr_names e).foldl (init := #[]) fun ds name =>
    if declared.any (·.core == name) then ds
    else
      -- Which program it would have belonged to, for the message. A left name
      -- spelled with a prime is rejected earlier, by the collision check.
      let (side, source) :=
        if name.endsWith "'" then ("right", name.dropEnd 1) else ("left", name)
      ds.push <| Message.withRange fr
        s!"`{source}` is not a variable of the {side} program" .userError

/-- Emit one bicommand: the left program's statements, then the right's, as
WhyRel's `Bisplit` does. **Per bicommand, not per side** — `(l₁|r₁); (l₂|r₂)`
becomes `l₁; r₁; l₂; r₂`, never `l₁; l₂; r₁; r₂`. The two are not
interchangeable: batching each side lets a *later* step of one program reach an
*earlier* obligation of the other, since an `assume` in a side moves across the
other side's statements. `docs/design.md` has the case. -/
def BodyState.emit (s : BodyState) (left right : List Core.Statement) : BodyState :=
  { s with out := s.out ++ left.toArray ++ right.toArray }

/-- Lower one bicommand, extending the accumulator. Each branch's binding
threading mirrors that form's `@[scope(…)]` in `Grammar.lean`. Under `project`,
one side is kept verbatim and nothing is primed or checked for collisions —
there is only one program, and Core checks it directly. -/
partial def lower_bicommand (mode : Mode) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (s : BodyState) (arg : Arg) : TransM BodyState := do
  match arg with
  | .op op =>
    let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) op.ann
    -- Each side's own range, so a collision points at the declaration.
    let src (a : Arg) : FileRange := { file := .file ictx.fileName, range := a.ann }
    -- A nested bicommand sequence, lowered into its own accumulator: its
    -- declarations are scoped to the Core block it becomes, so `declared` does
    -- not come back out. Counters do, to keep labels unique body-wide. `m` is
    -- a parameter because a `While` with alignment guards lowers its body three
    -- times — fused, and once per side, for the steps only one side takes.
    let seq_body (m : Mode) (st : BodyState) (a : Arg) : TransM BodyState := do
      match a with
      | .seq _ _ cs =>
        let mut b : BodyState := { st with out := #[] }
        for c in cs do
          b ← lower_bicommand m p ictx b c
        return b
      | _ => TransM.error "expected a sequence of bicommands"
    let keep (outer : BodyState) (b : BodyState) : BodyState :=
      { outer with asserts := b.asserts, assumes := b.assumes, diagnostics := b.diagnostics }
    -- `invariant { R }` clauses, labelled for the verifier's output.
    let invariants (st : BodyState) (tag : String) (a : Arg) :
        TransM (List (String × Core.Expression.Expr) × Array Message) := do
      match a with
      | .seq _ _ cs =>
        let mut out : List (String × Core.Expression.Expr) := []
        let mut ds : Array Message := #[]
        let mut i := 0
        for c in cs do
          match c with
          | .op op =>
            match op.args with
            | #[r] =>
              i := i + 1
              let e ← lower_rformula p st.bindings r
              ds := ds ++ check_formula st.declared (src c) e
              out := out ++ [(s!"{tag}_inv_{i}", e)]
            | _ => TransM.error "invariant does not hold exactly one relational formula"
          | _ => TransM.error "invariant is not an operation"
        return (out, ds)
      | _ => TransM.error "invariants are not a sequence"
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
                 out := (s.emit ls (prime_stmts (fragment_names rs) rs)).out }
      | .project .left => return { (s.emit ls []) with bindings := b }
      | .project .right => return { (s.emit rs []) with bindings := b }
    | q`RelRL.bi_var_left, #[l] =>
      let (ls, b) ← lower_decl_list p s.bindings l
      match mode with
      | .project .right => return { s with bindings := b }
      | .project .left => return { (s.emit ls []) with bindings := b }
      | .verify =>
        let s := s.declare (src l) .left (top_level_declared ls)
        return { (s.emit ls []) with bindings := b }
    | q`RelRL.bi_var_right, #[r] =>
      let (rs, b) ← lower_decl_list p s.bindings r
      let rnames := top_level_declared rs
      match mode with
      | .verify =>
        let s := s.declare (src r) .right rnames
        return { s with
                 bindings := b
                 out := (s.emit [] (prime_stmts (fragment_names rs) rs)).out }
      | .project .right => return { (s.emit rs []) with bindings := b }
      | .project .left => return { s with bindings := b }
    | q`RelRL.bi_sync, #[c] =>
      -- One statement; `lower_side` takes the sequence a split's side is.
      let (stmts, bindings) ← lower_side p s.bindings (.seq c.ann .newline #[c])
      let names := top_level_declared stmts
      match mode with
      | .verify =>
        -- One source name, declared into both programs.
        let s := (s.declare (src c) .left names).declare (src c) .right names
        -- One statement, run by both programs, so it must resolve in both.
        let s := (s.check_side (src c) .left stmts).check_side (src c) .right stmts
        return { s with
                 bindings := bindings
                 out := (s.emit stmts (prime_stmts (fragment_names stmts) stmts)).out }
      | .project _ =>
        return { (s.emit stmts []) with bindings := bindings }
    | q`RelRL.bi_embed, #[l, r] =>
      match mode with
      | .verify =>
        let (ls, _) ← lower_side p s.bindings l
        let (rs, _) ← lower_side p s.bindings r
        -- A split's declarations stay local to their side, but they land in the
        -- one fused block, so they still have to be unique in it.
        let s := (s.declare (src l) .left (top_level_declared ls)).declare
                   (src r) .right (top_level_declared rs)
        let s := (s.check_side (src l) .left ls).check_side (src r) .right rs
        return s.emit ls (prime_stmts (fragment_names rs) rs)
      | .project .left =>
        let (ls, _) ← lower_side p s.bindings l
        return s.emit ls []
      | .project .right =>
        let (rs, _) ← lower_side p s.bindings r
        return s.emit rs []
    | q`RelRL.bi_if_then, #[lg, rg, thn] =>
      -- WhyRel desugars the else-less form to an empty else; so does this, by
      -- passing an empty sequence on to the same branch.
      lower_bicommand mode p ictx s
        (.op { ann := op.ann, name := q`RelRL.bi_if,
               args := #[lg, rg, thn, .seq op.ann .newline #[]] })
    | q`RelRL.bi_if, #[lg, rg, thn, els] =>
      match mode with
      | .verify =>
        let lge ← translateExpr p s.bindings lg
        let rge ← translateExpr p s.bindings rg
        let rge := prime_expr (expr_names rge) rge
        -- Both sides are put under *one* Core `if`, which is faithful only
        -- because the guards are proved to agree first. That obligation is what
        -- WhyRel's rule for `If` requires to align the two branches at all.
        -- Take this `If`'s label before lowering the branches, so a nested one
        -- reads as the later obligation it is.
        let n := s.asserts + 1
        let s := { s with
                   asserts := n
                   diagnostics := s.diagnostics ++ check_formula s.declared (src lg) lge
                     ++ check_formula s.declared (src rg) rge }
        let t ← seq_body mode s thn
        let e ← seq_body mode (keep s t) els
        let s := keep s e
        let guards := bool_app Core.boolEquivOp [lge, rge]
        return { s with
                 out := s.out.push (.assert s!"if_guards_{n}" guards md)
                          |>.push (.ite (.det lge) t.out.toList e.out.toList md) }
      | .project side =>
        let g ← translateExpr p s.bindings (match side with | .left => lg | .right => rg)
        let t ← seq_body mode s thn
        let e ← seq_body mode (keep s t) els
        let s := keep s e
        return { s with out := s.out.push (.ite (.det g) t.out.toList e.out.toList md) }
    | q`RelRL.bi_if4, #[lg, rg, tt, te, et, ee] =>
      -- WhyRel's `Biif4`: the guards need not agree, so there is no agreement
      -- obligation — a branch per combination instead.
      let lge ← translateExpr p s.bindings lg
      let rge ← translateExpr p s.bindings rg
      match mode with
      | .verify =>
        let rge := prime_expr (expr_names rge) rge
        let s := { s with diagnostics := s.diagnostics
                     ++ check_formula s.declared (src lg) lge
                     ++ check_formula s.declared (src rg) rge }
        let a ← seq_body mode s tt
        let b ← seq_body mode (keep s a) te
        let c ← seq_body mode (keep s b) et
        let d ← seq_body mode (keep s c) ee
        let s := keep s d
        let notl := bool_app Core.boolNotOp [lge]
        let notr := bool_app Core.boolNotOp [rge]
        let inner : Core.Statement :=
          .ite (.det (bool_app Core.boolAndOp [notl, rge])) c.out.toList d.out.toList md
        let mid : Core.Statement :=
          .ite (.det (bool_app Core.boolAndOp [lge, notr])) b.out.toList [inner] md
        let outer : Core.Statement :=
          .ite (.det (bool_app Core.boolAndOp [lge, rge])) a.out.toList [mid] md
        return { s with out := s.out.push outer }
      | .project side =>
        -- `annot.ml`'s `projl`/`projr`: one side's guard picks between the two
        -- branches that agree on that side — then-then against else-then on the
        -- left, then-then against then-else on the right.
        let (g, thn, els) := match side with
          | .left => (lge, tt, et)
          | .right => (rge, tt, te)
        let a ← seq_body mode s thn
        let b ← seq_body mode (keep s a) els
        let s := keep s b
        return { s with out := s.out.push (.ite (.det g) a.out.toList b.out.toList md) }
    | q`RelRL.bi_while, #[lg, rg, la, ra, invs, body] =>
      -- WhyRel's general `Biwhile`, from `compile_biwhile` in translate.ml:
      --   while (lg || rg') invariant { align /\ … } {
      --     if (lg && la) then <left projection>
      --     else if (rg' && ra) then <right projection, primed>
      --     else <both sides>
      --   }
      -- The alignment condition is an invariant, not an assert: it is what
      -- rules out a state where one side must step and its guard forbids it.
      let lge ← translateExpr p s.bindings lg
      let rge ← translateExpr p s.bindings rg
      match mode with
      | .verify =>
        let rge := prime_expr (expr_names rge) rge
        let lae ← lower_rformula p s.bindings la
        let rae ← lower_rformula p s.bindings ra
        let n := s.asserts + 1
        let s := { s with asserts := n, diagnostics := s.diagnostics
                     ++ check_formula s.declared (src lg) lge
                     ++ check_formula s.declared (src rg) rge
                     ++ check_formula s.declared (src la) lae
                     ++ check_formula s.declared (src ra) rae }
        let (invEs, invDs) ← invariants s s!"while_{n}" invs
        let s := { s with diagnostics := s.diagnostics ++ invDs }
        let lock ← seq_body .verify s body
        let s := keep s lock
        -- The one-sided steps are this body's projections. Their diagnostics
        -- would repeat the fused pass's, so only that pass's are kept.
        let lonly ← seq_body (.project .left) { s with diagnostics := #[] } body
        let ronly ← seq_body (.project .right) { s with diagnostics := #[] } body
        let ronlyStmts := prime_stmts (fragment_names ronly.out.toList) ronly.out.toList
        let lstep := bool_app Core.boolAndOp [lge, lae]
        let rstep := bool_app Core.boolAndOp [rge, rae]
        let align := bool_app Core.boolOrOp
          [bool_app Core.boolOrOp [lstep, rstep],
           bool_app Core.boolOrOp
             [bool_app Core.boolAndOp [lge, rge],
              bool_app Core.boolAndOp
                [bool_app Core.boolNotOp [lge], bool_app Core.boolNotOp [rge]]]]
        let inner : Core.Statement :=
          .ite (.det lstep) lonly.out.toList
            [.ite (.det rstep) ronlyStmts lock.out.toList md] md
        let loop : Core.Statement :=
          .loop (.det (bool_app Core.boolOrOp [lge, rge])) none
            ((s!"while_{n}_align", align) :: invEs) [inner] md
        return { s with out := s.out.push loop }
      | .project side =>
        let b ← seq_body mode s body
        let s := keep s b
        let g := match side with | .left => lge | .right => rge
        return { s with out := s.out.push (.loop (.det g) none [] b.out.toList md) }
    | q`RelRL.bi_while_lockstep, #[lg, rg, invs, body] =>
      -- `compile_lockstep_biwhile`: one guard drives both sides, and the
      -- `lockstep` invariant is what makes that faithful.
      let lge ← translateExpr p s.bindings lg
      let rge ← translateExpr p s.bindings rg
      match mode with
      | .verify =>
        let rge := prime_expr (expr_names rge) rge
        let n := s.asserts + 1
        let s := { s with asserts := n, diagnostics := s.diagnostics
                     ++ check_formula s.declared (src lg) lge
                     ++ check_formula s.declared (src rg) rge }
        let (invEs, invDs) ← invariants s s!"while_{n}" invs
        let s := { s with diagnostics := s.diagnostics ++ invDs }
        let b ← seq_body mode s body
        let s := keep s b
        let lockstep := bool_app Core.boolEquivOp [lge, rge]
        let loop : Core.Statement :=
          .loop (.det lge) none (invEs ++ [(s!"while_{n}_lockstep", lockstep)])
            b.out.toList md
        return { s with out := s.out.push loop }
      | .project side =>
        let b ← seq_body mode s body
        let s := keep s b
        let g := match side with | .left => lge | .right => rge
        return { s with out := s.out.push (.loop (.det g) none [] b.out.toList md) }
    | q`RelRL.bi_while_left, #[g, invs, body] =>
      -- `compile_sided_biwhile`. WhyRel reaches this by writing `Biwhile` with
      -- the other guard false, so one side's guard drives the loop and the body
      -- is the whole bicommand — the user's body is what says the other side
      -- stands still. Projecting onto the *other* side gives `while false`,
      -- which is emitted as nothing.
      let ge ← translateExpr p s.bindings g
      match mode with
      | .verify =>
        let n := s.asserts + 1
        let s := { s with
                   asserts := n
                   diagnostics := s.diagnostics ++ check_formula s.declared (src g) ge }
        let (invEs, invDs) ← invariants s s!"while_{n}" invs
        let s := { s with diagnostics := s.diagnostics ++ invDs }
        let b ← seq_body mode s body
        let s := keep s b
        return { s with out := s.out.push (.loop (.det ge) none invEs b.out.toList md) }
      | .project .right => return s
      | .project .left =>
        let b ← seq_body mode s body
        let s := keep s b
        return { s with out := s.out.push (.loop (.det ge) none [] b.out.toList md) }
    | q`RelRL.bi_while_right, #[g, invs, body] =>
      let ge ← translateExpr p s.bindings g
      match mode with
      | .verify =>
        let ge := prime_expr (expr_names ge) ge
        let n := s.asserts + 1
        let s := { s with
                   asserts := n
                   diagnostics := s.diagnostics ++ check_formula s.declared (src g) ge }
        let (invEs, invDs) ← invariants s s!"while_{n}" invs
        let s := { s with diagnostics := s.diagnostics ++ invDs }
        let b ← seq_body mode s body
        let s := keep s b
        return { s with out := s.out.push (.loop (.det ge) none invEs b.out.toList md) }
      | .project .left => return s
      | .project .right =>
        let b ← seq_body mode s body
        let s := keep s b
        return { s with out := s.out.push (.loop (.det ge) none [] b.out.toList md) }
    | q`RelRL.bi_assert, #[r] =>
      match mode with
      | .project _ => return s
      | .verify =>
        let mut out := s.out
        let mut ds := s.diagnostics
        let mut i := 0
        for conjunct in top_conjuncts r do
          i := i + 1
          let e ← lower_rformula p s.bindings conjunct
          ds := ds ++ check_formula s.declared (src arg) e
          out := out.push (.assert s!"assert_{s.asserts + 1}_{i}" e md)
        return { s with out := out, asserts := s.asserts + 1, diagnostics := ds }
    | q`RelRL.bi_assume, #[r] =>
      -- Same shape as `bi_assert`: it has to observe both sides as they stand,
      -- `Statement.assume` in place of `.assert`.
      match mode with
      | .project _ => return s
      | .verify =>
        let mut out := s.out
        let mut ds := s.diagnostics
        let mut i := 0
        for conjunct in top_conjuncts r do
          i := i + 1
          let e ← lower_rformula p s.bindings conjunct
          ds := ds ++ check_formula s.declared (src arg) e
          out := out.push (.assume s!"assume_{s.assumes + 1}_{i}" e md)
        return { s with out := out, assumes := s.assumes + 1, diagnostics := ds }
    | n, args =>
      TransM.error s!"unexpected bicommand {n.fullName} with {args.size} arguments"
  | _ => TransM.error "biproc body element is not an operation"

/-- Spec clauses to Core statements — `assume` for `requires`, `assert` for
`ensures` — one per top-level conjunct. A projection drops both. -/
def lower_spec_clauses (mode : Mode) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (bindings : TransBindings) (declared : List DeclName)
    (kind : String) (assumed : Bool) (arg : Arg) :
    TransM (Array Core.Statement × Array Message) := do
  match mode, arg with
  | .project _, _ => return (#[], #[])
  | _, .seq _ _ clauses =>
    let mut out : Array Core.Statement := #[]
    let mut ds : Array Message := #[]
    let mut n := 0
    for clause in clauses do
      match clause with
      | .op op =>
        let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) op.ann
        let fr : FileRange := { file := .file ictx.fileName, range := op.ann }
        match op.args with
        | #[r] =>
          for conjunct in top_conjuncts r do
            n := n + 1
            let e ← lower_rformula p bindings conjunct
            ds := ds ++ check_formula declared fr e
            out := out.push <|
              if assumed then .assume s!"{kind}_{n}" e md else .assert s!"{kind}_{n}" e md
        | _ => TransM.error s!"{kind} clause does not hold exactly one relational formula"
      | _ => TransM.error s!"{kind} clause is not an operation"
    return (out, ds)
  | _, _ => TransM.error s!"biproc's {kind} argument is not a sequence"

/-- Each side's parameters, as a Core `Bindings`. `translateProcBindings` does
the work — including `out`/`inout` — and the right side's names are then primed,
like every other right-side name. Also returns them as `DeclName`s, so the
per-side checks in the body treat a parameter as declared.

Under `project` only the kept side survives, unprimed: the printed program is
that side alone. -/
def lower_params (mode : Mode) (top : TransBindings) (params : Arg) :
    TransM (@Lambda.LMonoTySignature Unit × @Lambda.LMonoTySignature Unit × List DeclName × TransBindings) := do
  match params with
  | .option _ none => return ([], [], [], top)
  | .option _ (some (.op op)) =>
    match op.args with
    | #[l, r] =>
      let (li, lo, b) ← translateProcBindings top l
      let (ri, ro, b) ← translateProcBindings b r
      let prime (sig : @Lambda.LMonoTySignature Unit) : @Lambda.LMonoTySignature Unit :=
        sig.map fun (id, ty) => (⟨id.name ++ "'", ()⟩, ty)
      let names (side : Side) (sig : @Lambda.LMonoTySignature Unit) : List DeclName :=
        sig.map fun (id, _) => ⟨side.core_name id.name, id.name, side⟩
      let declared := names .left li ++ names .left lo ++ names .right ri ++ names .right ro
      match mode with
      | .verify => return (li ++ prime ri, lo ++ prime ro, declared, b)
      | .project .left => return (li, lo, declared, b)
      | .project .right => return (ri, ro, declared, b)
    | _ => TransM.error "biproc parameters are not a left/right pair"
  | _ => TransM.error "biproc parameters are not an option"

/-- `requires` assumptions, then the bicommands, then the `ensures` obligations.
`requires` is lowered against the *incoming* bindings, matching its lack of
`@[scope(…)]`; `ensures` against what the body ends with. -/
def lower_biproc (mode : Mode) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (top : TransBindings)
    (params : Arg) (reqs : Arg) (body : Arg) (ens : Arg) :
    TransM (@Lambda.LMonoTySignature Unit × @Lambda.LMonoTySignature Unit ×
            List Core.Statement × Array Message) := do
  match body with
  | .seq _ _ bicommands =>
    let (inputs, outputs, ps, top) ← lower_params mode top params
    -- `requires` is scoped to the parameters, not the body: a precondition can
    -- name what the caller supplies and nothing the body declares.
    let (pre, preDiags) ← lower_spec_clauses mode p ictx top ps "requires" true reqs
    let mut st : BodyState := { bindings := top, declared := ps }
    for bicommand in bicommands do
      st ← lower_bicommand mode p ictx st bicommand
    let done := st
    let (post, postDiags) ←
      lower_spec_clauses mode p ictx done.bindings done.declared "ensures" false ens
    return (inputs, outputs, (pre ++ done.out ++ post).toList,
            done.diagnostics ++ preDiags ++ postDiags)
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
      | #[.ident _ name, params, reqs, body, ens] =>
        let ((inputs, outputs, stmts, sourceErrors), errors) :=
          TransM.run ictx (lower_biproc mode p ictx top params reqs body ens) p.globalContext
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
          { header := { name := name, typeArgs := [], inputs := inputs, outputs := outputs },
            spec := { preconditions := [], postconditions := [] },
            body := .structured [block] } md] :: procs
      | _ =>
        emit_invariant_violation "biproc does not have exactly five arguments"
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
