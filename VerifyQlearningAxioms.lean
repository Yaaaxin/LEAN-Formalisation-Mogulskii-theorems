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
#print axioms Qlearning.smallStepLDP_of_equivalent
#print axioms Qlearning.smallStepLDP_map_injective
#print axioms Qlearning.offGridNoise_apply
#print axioms Qlearning.offGridNoise_distance
#print axioms Qlearning.maximum_increment_smallStep
#print axioms Qlearning.iid_offGrid_smallStep_mogulskii
#print axioms Qlearning.controlled_smallStep_mogulskii
#print axioms Qlearning.windowLDP_of_deterministic_estimates

open Lean in
run_cmd do
  for theoremName in [``Qlearning.iid_fixedWindow_mogulskii,
      ``Qlearning.controlledWindow_mogulskii, ``Qlearning.windowLDP_arbitrary_steps,
      ``Qlearning.maximum_increment_superexponential,
      ``Qlearning.tracking_implies_superexponential,
      ``Qlearning.exponentialBounds_of_equivalent, ``Qlearning.euler_fixedWindow_LDP,
      ``Qlearning.iid_canonical_smallStep_mogulskii,
      ``Qlearning.smallStepLDP_of_equivalent, ``Qlearning.smallStepLDP_map_injective,
      ``Qlearning.offGridNoise_apply, ``Qlearning.offGridNoise_distance,
      ``Qlearning.maximum_increment_smallStep, ``Qlearning.iid_offGrid_smallStep_mogulskii,
      ``Qlearning.controlled_smallStep_mogulskii,
      ``Qlearning.windowLDP_of_deterministic_estimates] do
    let unexpected := (← collectAxioms theoremName).filter fun axiomName =>
      axiomName != ``propext && axiomName != ``Classical.choice && axiomName != ``Quot.sound
    unless unexpected.isEmpty do
      throwError m!"'{theoremName}' depends on unexpected axioms: {unexpected.toList}"
