import Qlearning
import Lean.Util.CollectAxioms

#print axioms Qlearning.iid_fixedWindow_mogulskii
#print axioms Qlearning.controlledWindow_mogulskii
#print axioms Qlearning.windowLDP_arbitrary_steps
#print axioms Qlearning.maximum_increment_superexponential
#print axioms Qlearning.tracking_implies_superexponential
#print axioms Qlearning.exponentialBounds_of_equivalent
#print axioms Qlearning.euler_fixedWindow_LDP
#print axioms Qlearning.iid_canonical_smallStep_mogulskii

open Lean in
run_cmd do
  for theoremName in [``Qlearning.iid_fixedWindow_mogulskii,
      ``Qlearning.controlledWindow_mogulskii, ``Qlearning.windowLDP_arbitrary_steps,
      ``Qlearning.maximum_increment_superexponential,
      ``Qlearning.tracking_implies_superexponential,
      ``Qlearning.exponentialBounds_of_equivalent, ``Qlearning.euler_fixedWindow_LDP,
      ``Qlearning.iid_canonical_smallStep_mogulskii] do
    let unexpected := (← collectAxioms theoremName).filter fun axiomName =>
      axiomName != ``propext && axiomName != ``Classical.choice && axiomName != ``Quot.sound
    unless unexpected.isEmpty do
      throwError m!"'{theoremName}' depends on unexpected axioms: {unexpected.toList}"
