/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Translate.Formulas
public import RelRL.DDMTransform.Translate.State
public import Strata.Languages.Core.Verifier
public import Strata.DL.Imperative.MetaData
public import Strata.Pipeline.Messages
import StrataDDM.AST

namespace Strata
namespace RelRL

public section

open StrataDDM (Arg)

/-! # What both lowerings are built from

A bicommand's sides hold Core syntax, so lowering one means handing a fragment
back to Core's own translator; the checks over the result are here too. Nothing
here reads `Mode` — `Projection.lean` and `Composition.lean` do. -/

/-- Lower one side's statements. The synthetic `Core.block` wrap is all
`translateBlock` needs; `bindings` is the scope the side was elaborated in. -/
def lower_side (p : StrataDDM.Program) (bindings : TransBindings) (arg : Arg) :
    TransM (List Core.Statement × TransBindings) := do
  match arg with
  | .seq ann _ stmts =>
    translateBlock p bindings
      (.op { ann, name := q`Core.block, args := #[.seq ann .newline stmts] })
  | _ => TransM.error "bicommand side is not a statement sequence"

/-- Lower a `Var` side's `DeclList`, by putting it back in the
`Core.varStatement` Core's grammar wraps it in. Nothing is initialized. -/
def lower_decl_list (p : StrataDDM.Program) (bindings : TransBindings) (dl : Arg) :
    TransM (List Core.Statement × TransBindings) := do
  let ann := dl.ann
  let stmt : Arg := .op { ann, name := q`Core.varStatement, args := #[.option ann none, dl] }
  translateBlock p bindings
    (.op { ann, name := q`Core.block, args := #[.seq ann .newline #[stmt]] })


/-- The `biproc` a synchronized call names, if this file declares one. A unary
`procedure` is not one: it is called from inside a side, through Core's `call`.
-/
def find_biproc (p : StrataDDM.Program) (name : String) : Option StrataDDM.Operation :=
  p.commands.find? fun op =>
    op.name == q`RelRL.biproc &&
      (match (op.args[0]? : Option Arg) with
       | some (.ident _ n) => n == name
       | _ => false)

/-- One side of a synchronized call, lowered by putting it back in the
`Core.call_statement` Core's grammar wraps it in — so `out`/`inout` arguments go
through Core's own translator rather than a second copy of it here. -/
def lower_call_side (p : StrataDDM.Program) (bindings : TransBindings)
    (name : Arg) (args : Arg) : TransM Core.Statement := do
  let ann := args.ann
  let stmt : Arg := .op { ann, name := q`Core.call_statement,
                          args := #[.option ann none, name, args] }
  match ← translateStmt p bindings stmt with
  | ([st], _) => return st
  | _ => TransM.error "a call statement did not lower to exactly one Core statement"

/-- The callee's parameter counts, per side: value arguments, then results. An
`inout` counts as both, exactly as it does at the call site. -/
def biproc_arity (bindings : TransBindings) (params : Arg) :
    TransM ((Nat × Nat) × (Nat × Nat)) := do
  match params with
  | .option _ none => return ((0, 0), (0, 0))
  | .option _ (some (.op op)) =>
    match op.args with
    | #[l, r] =>
      let (li, lo, b) ← translateProcBindings bindings l
      let (ri, ro, _) ← translateProcBindings b r
      return ((li.length, lo.length), (ri.length, ro.length))
    | _ => TransM.error "biproc parameters are not a left/right pair"
  | _ => TransM.error "biproc parameters are not an option"

/-- How many arguments and results a lowered call passes. -/
def call_counts : Core.Statement → Nat × Nat
  | .call _ args _ =>
    ((Core.CallArg.getInputExprs args).length, (Core.CallArg.getLhs args).length)
  | _ => (0, 0)

/-- Check one side's argument list against the callee's parameters. Core checks
this too, but only after the two sides have been fused into one argument list,
so its message names neither the side nor a source position. -/
def check_call_arity (callee : String) (side : Side) (fr : FileRange)
    (want got : Nat × Nat) : Array Message :=
  if want == got then #[] else
    #[Message.withRange fr
        s!"`{callee}`'s {side.name} side takes {want.1} argument(s) and {want.2} \
           result(s); this call passes {got.1} and {got.2}" .userError]

/-- Refuse a Core declaration anywhere inside a side — nested in an `if` or
`while` body included. `Var` is the only form that declares, as in WhyRel, whose
`|_ … _|` takes an `atomic_command` and whose only binder is `Var … in CC`.

Nesting is refused rather than left alone because it is not actually safe: two
sibling blocks declaring one name make Core drop every obligation in the
procedure, silently and with exit 0 — [`issues.md`](issues.md), "Sibling blocks
sharing a declared name lose every obligation". Each bicommand emits into one
flat block, so two bicommands' `if`s are siblings and one repeated name reaches
it. -/
def refuse_declarations (fr : FileRange) (what : String)
    (stmts : List Core.Statement) : Array Message :=
  let declared := (Imperative.HasVarsImp.definedVars (P := Core.Expression) stmts false)
    |>.map (·.name) |>.eraseDups
  declared.foldl (init := #[]) fun ds name =>
    ds.push <| Message.withRange fr
      s!"`{name}` cannot be declared inside {what}: `Var` is the only form that \
         declares. Write `Var {name} : … | … ;` before the bicommand." .userError

/-- A synchronized call naming something no `biproc` in this file answers. -/
def unknown_callee (fr : FileRange) (callee : String) : Message :=
  Message.withRange fr
    s!"`{callee}` is not a `biproc` declared in this file. A unary `procedure` \
       is called from inside a side — `|- call {callee}(…); -| ;` — and relates \
       the two programs through its own spec." .userError

/-- Where a synchronized `biproc` call sits inside a bicommand tree, if one
does. `bi_while` lowers its body through `.project` to get the steps only one
side takes, and a `biproc` has no unary contract for those steps to call —
`docs/status.md` says what to write instead. -/
partial def bi_call_inside? (a : Arg) : Option StrataDDM.SourceRange :=
  match a with
  | .op op =>
    if op.name == q`RelRL.bi_call then some op.ann else op.args.findSome? bi_call_inside?
  | .seq _ _ as => as.findSome? bi_call_inside?
  | .option _ (some b) => bi_call_inside? b
  | _ => none

/-- What a nested bicommand sequence hands back. Its declarations are scoped to
the Core block it becomes, so `declared` does not come out; the counters do, to
keep labels unique body-wide. -/
def keep (outer : BodyState) (b : BodyState) : BodyState :=
  { outer with asserts := b.asserts, assumes := b.assumes, diagnostics := b.diagnostics }
end
end RelRL
end Strata
