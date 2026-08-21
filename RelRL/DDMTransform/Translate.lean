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

/-! # RelRL → Core translation

`biembed left right` lowers to a single Core statement block containing two
labeled sub-blocks, `left` followed by `right`, executed as one sequential
Core program: left and right remain separate namespaces (Core scoping, not
aliasing), matching the RelRl-inspired design of this dialect discussed
during development (no shared heap/state is introduced between the two
sides).

Every other top-level `Command` in an RelRL program is ordinary Core syntax
(the RelRL grammar only *extends* Core's `Command` category with
`command_bicommand`), so it is translated by delegating straight to Core's
own DDM translator (`Core.getProgram`), reusing exactly the same
battle-tested per-statement/per-declaration translation Core itself uses
instead of re-implementing it. -/

structure TranslateState where
  diagnostics : Array Message := #[]

abbrev TranslateM := StateM TranslateState

def TranslateM.run (m : TranslateM α) : α × Array Message :=
  let (v, s) := StateT.run m {}
  (v, s.diagnostics)

def emitDiagnostic (d : Message) : TranslateM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics.push d }

/-- Translate an ordinary Core-syntax top-level operation (a function,
procedure, type declaration, or bare block) by delegating to Core's own DDM
translator. The operation is wrapped in a singleton Core program so that
`Core.getProgram` can be reused unchanged. -/
def translateCoreOp (op : Operation) (ictx : Lean.Parser.InputContext) :
    TranslateM (List Core.Decl) := do
  let singleton := StrataDDM.Program.create Core_map "Core" #[op]
  let (coreProgram, errors) := Core.getProgram singleton ictx
  for e in errors do
    emitDiagnostic (Message.fromString e .strataBug)
  return coreProgram.decls

/-- Extract the single statement produced by translating one side (`left` or
`right`) of a `biembed`. A bare block on that side translates (via Core's own
`command_block` handling) to a single nameless, parameterless procedure whose
body is the block's statements; we unwrap that back into a plain statement
list to embed inside the combined `biembed` block. -/
def extractSideStatements (label : String) (decls : List Core.Decl) :
    TranslateM (List Core.Statement) := do
  match decls with
  | [.proc proc _md] =>
    match proc.body with
    | .structured ss => return ss
    | .cfg _ =>
      emitDiagnostic (Message.fromString
        s!"biembed {label} side must be structured Core syntax, not a CFG block")
      return []
  | _ =>
    emitDiagnostic (Message.fromString
      s!"biembed {label} side must be a single Core statement block")
    return []

mutual

/-- Lower a `biembed` operation's two `Command`-typed arguments (`left`,
`right`) to a single Core sequence/block: a "biembed" block containing a
"left" sub-block followed by a "right" sub-block. -/
partial def lowerBicommand (op : Operation) (ictx : Lean.Parser.InputContext) :
    TranslateM Core.Statement := do
  match op.args with
  | #[left, right] =>
    let leftStmt ← lowerCommandArg "left" left ictx
    let rightStmt ← lowerCommandArg "right" right ictx
    let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) op.ann
    return .block "biembed" [leftStmt, rightStmt] md
  | _ =>
    emitDiagnostic (Message.fromString "biembed expects exactly two commands (left, right)")
    return .block "biembed" [] {}

/-- Lower a single `Command`-typed argument: either a nested bicommand
(`RelRL.command_bicommand`, itself wrapping `biembed` or a future relational
operator) or ordinary Core syntax. -/
partial def lowerCommandArg (label : String) (arg : Arg) (ictx : Lean.Parser.InputContext) :
    TranslateM Core.Statement := do
  match arg with
  | .op op => lowerCommandOp label op ictx
  | _ =>
    emitDiagnostic (Message.fromString s!"biembed {label} side must be a command")
    return .block label [] {}

partial def lowerCommandOp (label : String) (op : Operation) (ictx : Lean.Parser.InputContext) :
    TranslateM Core.Statement := do
  if op.name == q`RelRL.command_bicommand then
    match op.args with
    | #[.op bicommandOp] => lowerBicommand bicommandOp ictx
    | _ =>
      emitDiagnostic (Message.fromString s!"malformed bicommand on {label} side")
      return .block label [] {}
  else
    let decls ← translateCoreOp op ictx
    let stmts ← extractSideStatements label decls
    return .block label stmts {}

end

/-- Translate a whole RelRL program to Core: each top-level `RelRL.command_bicommand`
becomes a nameless Core procedure whose body is the lowered `biembed` block;
every other top-level command is ordinary Core syntax, translated unchanged
via `Core.getProgram`. -/
def translateProgram (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext := Inhabited.default) : TranslateM Core.Program := do
  let mut decls : List Core.Decl := []
  for op in p.commands do
    if op.name == q`RelRL.command_bicommand then
      match op.args with
      | #[.op bicommandOp] =>
        let stmt ← lowerBicommand bicommandOp ictx
        let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) op.ann
        decls := decls ++ [.proc
          { header := { name := "", typeArgs := [], inputs := [], outputs := [] },
            spec := { preconditions := [], postconditions := [] },
            body := .structured [stmt] } md]
      | _ =>
        emitDiagnostic (Message.fromString "malformed top-level bicommand")
    else
      let subDecls ← translateCoreOp op ictx
      decls := decls ++ subDecls
  return { decls := decls }

end
end RelRL
end Strata
