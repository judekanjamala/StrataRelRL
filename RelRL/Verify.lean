/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Translate
public import Strata.Languages.Core
public import Strata.Pipeline.Messages
public import StrataDDM.Integration.Lean

namespace Strata
namespace RelRL

public section

-- `Core` alone is ambiguous here: `Strata.Core` names the generated
-- `StrataDDM.Dialect` value and shadows the `Core` *namespace* holding
-- `Core.Program`, `Core.VCResult`. Hence the `_root_.Core.` prefixes below.

/-- Translate `p` to Core, then verify it via `Strata.Core.verifyProgram` —
Core's tempDir/vcDirectory handling, SMT discharge and `VCResults` reporting,
unchanged. Translation diagnostics come back alongside the results.

A fatal diagnostic means the Core program is not the one the source denotes, so
verification is skipped: `verifyProgram` throws on such a program, and that
exception would bury the located diagnostic that explains it. -/
def verify (p : StrataDDM.Program) (ictx : Lean.Parser.InputContext := Inhabited.default)
    (options : _root_.Core.VerifyOptions := .default) :
    IO (_root_.Core.VCResults × Array Message) := do
  let (coreProgram, diagnostics) := TranslateM.run (translate_program p ictx)
  if diagnostics.any (fun d => d.kind.impact.isFatal) then
    return (#[], diagnostics)
  let vcResults ← EIO.toIO (fun m => IO.Error.userError m)
    (Strata.Core.verifyProgram coreProgram options)
  return (vcResults, diagnostics)

/-- Convenience wrapper returning only formatted `Message`s (translation
diagnostics plus one message per proof obligation), for CLI-style reporting. -/
def verify_to_messages (p : StrataDDM.Program) (ictx : Lean.Parser.InputContext := Inhabited.default)
    (options : _root_.Core.VerifyOptions := .default) : IO (Array Message) := do
  let (vcResults, diagnostics) ← verify p ictx options
  let vcMessages := vcResults.map fun vcr =>
    let fr := (Imperative.getFileRange vcr.obligation.metadata).getD FileRange.unknown
    let kind : MessageKind := if vcr.isSuccess then .warning else .userError
    Message.withRange fr s!"[{vcr.obligation.label}]: {vcr.formatOutcome}" kind
  return diagnostics ++ vcMessages

end
end RelRL
end Strata
