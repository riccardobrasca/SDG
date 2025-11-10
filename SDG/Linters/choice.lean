import Lean.Util.CollectAxioms
import Mathlib.Tactic.DeclarationNames

/-!
#  The "detectClassical" linter

The "detectClassical" linter emits a warning on declarations that depend on the `Classical.choice`
axiom.
-/

open Lean Elab Linter Command

namespace Mathlib.Linter

/--
The "detectClassical" linter emits a warning on declarations that depend on the `Classical.choice`
axiom.
-/
register_option linter.detectClassical : Bool := {
  defValue := true
  descr := "enable the detectClassical linter"
}

/--
The `linter.verbose.detectClassical` option is a flag to make the `detectClassical` linter emit
a confirmation on declarations that depend *not* on the `Classical.choice` axiom.
-/
register_option linter.verbose.detectClassical : Bool := {
  defValue := false
  descr := "enable the verbose setting for the detectClassical linter"
}

namespace DetectClassical

@[inherit_doc Mathlib.Linter.linter.detectClassical]
def detectClassicalLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.detectClassical (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let nms := (← getNamesFrom (stx.getPos?.getD default)).filter (! ·.getId.isInternal)
  let verbose? := Linter.getLinterValue linter.verbose.detectClassical (← getLinterOptions)
  for constStx in nms do
    let constName := constStx.getId
    let axioms ← collectAxioms constName
    if !axioms.contains `Classical.choice then return
    else
      Linter.logLint linter.detectClassical constStx
        m!"'{constName}' depends on 'Classical.choice'.\n\nAll axioms: {axioms.toList}\n"

initialize addLinter detectClassicalLinter

end DetectClassical

end Mathlib.Linter
