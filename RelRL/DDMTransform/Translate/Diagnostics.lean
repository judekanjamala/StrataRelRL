/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Pipeline.Messages

namespace Strata
namespace RelRL

public section

/-! # Translation diagnostics

`TranslateM` collects `Message`s instead of panicking, so a broken invariant or
an error in the source program is reported with a position rather than aborting
the run. `RelRL/Cli/Common.lean` decides what each kind exits with. -/

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

end
end RelRL
end Strata
