/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Grammar
public import RelRL.DDMTransform.Translate.Bicommands
public import RelRL.DDMTransform.Translate.Diagnostics
public import Strata.Languages.Core.Verifier
public import Strata.DL.Imperative.MetaData
public import Strata.Pipeline.Messages
import StrataDDM.AST

namespace Strata
namespace RelRL

public section

open StrataDDM (Operation Arg)

/-! # From a `biproc` to a Core program

A `biproc` becomes a Core procedure holding both programs at once: the left side
keeps its source names, every right-side name is primed, and a relational formula
is then an ordinary Core `assert` over both.

Lowering runs inside Core's `TransM`, threading its `TransBindings` from one
side to the next. **That threading mirrors the `@[scope(…)]` chain in
`Grammar.lean` and must be kept in step with it** — see CLAUDE.md, "The other
invariant". `docs/workflows/pipeline.md` walks the stages; `docs/design.md`
argues the choices.
-/

/-- Spec clauses to Core statements — `assume` for `requires`, `assert` for
`ensures` — one per top-level conjunct. A projection drops both. -/
def lower_spec_clauses (mode : Mode) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (bindings : TransBindings) (declared : List DeclName)
    (kind : String) (arg : Arg) :
    TransM (ListMap Core.CoreLabel Core.Procedure.Check × Array Message) := do
  match mode, arg with
  | .project _, _ => return ([], #[])
  | _, .seq _ _ clauses =>
    let mut out : ListMap Core.CoreLabel Core.Procedure.Check := []
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
            let entry : Core.CoreLabel × Core.Procedure.Check :=
              (s!"{kind}_{n}", { expr := e, md := md })
            out := out.append [entry]
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
        sig.map fun (id, _) => ⟨side.core_name id.name, id.name, side, true⟩
      let declared := names .left li ++ names .left lo ++ names .right ri ++ names .right ro
      match mode with
      | .verify => return (li ++ prime ri, lo ++ prime ro, declared, b)
      | .project .left => return (li, lo, declared, b)
      | .project .right => return (ri, ro, declared, b)
    | _ => TransM.error "biproc parameters are not a left/right pair"
  | _ => TransM.error "biproc parameters are not an option"

/-- The procedure a `biproc` becomes: its signature, its contract, and its body.

Both clauses are lowered against the parameters alone — never the body's
bindings — so a spec cannot name a bi-local, and Core's own pre/postconditions
are what they become. That is what gives `old x` its meaning: the entry value of
an `inout` parameter. A claim about a bi-local belongs in an `Assert { R }` in
the body, where it is checked where it stands. -/
def lower_biproc (mode : Mode) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (top : TransBindings)
    (params : Arg) (reqs : Arg) (ens : Arg) (body : Arg) :
    TransM (@Lambda.LMonoTySignature Unit × @Lambda.LMonoTySignature Unit ×
            Core.Procedure.Spec × List Core.Statement × Array Message) := do
  match body with
  | .seq _ _ bicommands =>
    let (inputs, outputs, ps, top) ← lower_params mode top params
    let (pre, preDiags) ← lower_spec_clauses mode p ictx top ps "requires" reqs
    let (post, postDiags) ← lower_spec_clauses mode p ictx top ps "ensures" ens
    let mut st : BodyState := { bindings := top, declared := ps }
    for bicommand in bicommands do
      st ← lower_bicommand mode p ictx st bicommand
    return (inputs, outputs, { preconditions := pre, postconditions := post },
            st.out.toList, st.diagnostics ++ preDiags ++ postDiags)
  | _ => TransM.error "biproc body is not a sequence of bicommands"

/-- Commands that add more than one `freeVars` entry per decl they return, and
so break the index alignment `translate_program_with` depends on. Names what was
found, for the message. `docs/issues.md`, "A `datatype` breaks the top-level
binding list" — delete this once that is fixed upstream. -/
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
  -- `Core_map` holds Core and its imports, not `RelRL`. Sound only because
  -- `biproc` is filtered out above and no bicommand is reachable at top level;
  -- a second top-level RelRL operator would need the real dialect map threaded
  -- through from `build_relrl_dialect_file_map`.
  let coreProgram := StrataDDM.Program.create Core_map "Core" coreCommands
  let (coreDecls, coreErrors) :=
    TransM.run ictx (translateCoreDecls coreProgram {}) p.globalContext
  for e in coreErrors do
    emit_diagnostic (Message.fromString e .strataBug)
  -- Holds only while each command contributes exactly one decl.
  -- `command_datatypes` and a multi-function `command_recfndefs` add more
  -- `freeVars` entries than that, making this array shorter than the index
  -- space a `.fvar i` in a body resolves against; `misaligning_command?` below
  -- refuses those two. `docs/issues.md`, "A `datatype` breaks the top-level
  -- binding list".
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
      | #[.ident _ name, params, reqs, ens, body] =>
        let ((inputs, outputs, spec, stmts, sourceErrors), errors) :=
          TransM.run ictx (lower_biproc mode p ictx top params reqs ens body) p.globalContext
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
            spec := spec,
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
