/- 
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RRL.DDMTransform.Translate
public import Strata.Languages.Core
public import Strata.Pipeline.Messages
public import StrataDDM.Integration.Lean

namespace Strata
namespace RRL

public section

-- `Core` alone is ambiguous here: `Strata.Core` also names the generated
-- `StrataDDM.Dialect` value for the Core dialect (declared by `#dialect
-- ... #end` in `Strata.Languages.Core.DDMTransform.Grammar`), which shadows
-- the `Core` *namespace* holding `Core.Program`, `Core.VCResult`, etc. Use
-- fully-qualified names throughout to avoid the ambiguity.

/-- Translate `p` (an RRL `StrataDDM.Program`) to Core, then verify it exactly
the way `Strata.Core.verifyProgram` verifies any other Core program: this
reuses Core's existing tempDir/vcDirectory handling, SMT discharge, and
`VCResults` reporting unchanged. Translation-time diagnostics from the RRL
lowering (see `RRL.DDMTransform.Translate`) are returned alongside the
`VCResults` so callers can report both in one place. -/
def verify (p : StrataDDM.Program) (ictx : Lean.Parser.InputContext := Inhabited.default)
    (options : _root_.Core.VerifyOptions := .default) :
    IO (_root_.Core.VCResults × Array Message) := do
  let (coreProgram, diagnostics) := TranslateM.run (translateProgram p ictx)
  let vcResults ← EIO.toIO (fun m => IO.Error.userError m)
    (Strata.Core.verifyProgram coreProgram options)
  return (vcResults, diagnostics)

/-- Convenience wrapper returning only formatted `Message`s (translation
diagnostics plus one message per proof obligation), for CLI-style reporting. -/
def verifyToMessages (p : StrataDDM.Program) (ictx : Lean.Parser.InputContext := Inhabited.default)
    (options : _root_.Core.VerifyOptions := .default) : IO (Array Message) := do
  let (vcResults, diagnostics) ← verify p ictx options
  let vcMessages := vcResults.map fun vcr =>
    let fr := (Imperative.getFileRange vcr.obligation.metadata).getD FileRange.unknown
    let kind : MessageKind := if vcr.isSuccess then .warning else .userError
    Message.withRange fr s!"[{vcr.obligation.label}]: {vcr.formatOutcome}" kind
  return diagnostics ++ vcMessages

end
end RRL
end Strata
