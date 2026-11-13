# Mogulskii interface for the Q-learning paper

This extension connects the existing finite-dimensional path LDP to the fixed-window argument in Appendix B.1 of *Local Moment Agreement Does Not Preserve Decision Exponents in Coupled Q-Learning*. The actual small-step noise LDP is proved. The trajectory and Euler conclusions are conditional on the explicitly stated deterministic estimates; the stationary LDP and the whole paper are not claimed to be formalized.

## Mathematical objects

The noise is an IID sequence `X k` with values in Euclidean `d`-space. It is measurable and has finite exponential moments in every direction. Centering and positive definite covariance, which the paper also assumes, are not needed for Mogulskii's theorem itself.

Paths are continuous maps on `[0,1]` with the uniform norm. On a physical window of length `T > 0`, the argument `s` represents physical time `T*s`. For the exact mesh `alpha = T/n`, the noise path is `T * interpolate X n`. Its physical action is

```
windowAction T zeta = T * pathRate(cramerRate)(zeta / T).
```

The pre-existing `pathRate` is an infimum over integrable velocities whose primitives equal the path, with cost the integral of the Cramer rate. It is infinite when no such velocity exists. Thus the initial value at zero and absolute-continuity restriction are present in the rate, rather than omitted from a simplified statement.

## Coverage

| Paper step | Declaration | Scope |
| --- | --- | --- |
| Mogulskii on a fixed positive window | `iid_fixedWindow_mogulskii` | Proved for the exact meshes `alpha = T/n`. Both open and closed LDP bounds and the good-rate property are returned, allowing infinite rates and zero event probabilities. |
| Speed and action conversion | `speedNLDP_to_windowLDP` | Proves that speed `n` and action `I` become speed `n/T` and action `T*I`. |
| Shared-driver contraction | `controlled_smallStep_mogulskii` | Proves the actual-step LDP and good-rate property for a continuous solution map with a driver-recovery identity. These deterministic inputs remain explicit. The action is paid once for the shared driver. |
| Actual off-grid noise LDP | `iid_offGrid_smallStep_mogulskii` | Proved for the actual alpha-grid noise polygon on every fixed positive window and every positive vanishing step family. No off-grid comparison is assumed. |
| Actual path identification | `offGridNoise_apply` | Proves the alpha times partial-sum plus fractional-increment formula at physical time T*s. |
| Off-grid distance estimate | `offGridNoise_distance` | Proves a uniform bound of twice alpha times the largest relevant increment; no numerical check replaces this proof. |
| Real-valued step rescaling | `windowLDP_arbitrary_steps` | Proves the LDP for the canonical reference laws at `n = floor(T/alpha)+1` along any positive vanishing step family, indexed by any filter. It proves the required count divergence and `alpha*n/T -> 1`; it does not identify those reference paths with the actual off-grid recursion. |
| Large individual increments | `maximum_increment_superexponential` | Proves the super-exponential tail for the largest of `n+1` increments from the directional exponential-moment assumptions. |
| Consequence of the Euler estimate | `tracking_implies_superexponential` | Given a deterministic `C/n` times maximum-increment bound, proves exponential equivalence. The deterministic ODE/Euler estimate itself is an input, not assumed to have been formalized. |
| Actual Euler window LDP, conditional on deterministic estimates | `windowLDP_of_deterministic_estimates` | Combines the actual noise LDP, shared-driver contraction, real-step tracking transfer and good rates. Its inputs explicitly include the solution-map continuity/recovery identity and the Euler error estimate. |
| Real-step exponential-equivalence transfer | `smallStepLDP_of_equivalent` | Proves transfer along any index filter at speed 1/alpha. The integer-mesh version is also retained. |

## Obligations that are still outside this extension

1. Construct the specific Bellman-max solution map and prove its continuity estimate and recovery identity from the integral equation. These are the deterministic results of Lemma B.1.
2. Prove the deterministic Euler tracking estimate for the actual coupled Q-learning recursion, as in Lemma B.2.
3. The stationary tail, sandwich, last-exit argument and stationary limit of Appendix B.2--B.3 are not part of this extension.

The conditional trajectory theorem cannot be described as an unconditional formalization of the specific Bellman-max recursion in Lemma B.3. Its probability argument, including the actual off-grid process, is proved; constructing that particular solution map and its Euler estimate remains outside this extension. The noise theorem, time-scale conversion and tail estimates have only their standard probabilistic assumptions.

The solution map is defined on all continuous drivers for the contraction argument. A suitable integral-equation extension uses initial value q* + b*zeta(0) off the zero-start subspace; finite-action drivers necessarily have zeta(0) = 0. A map that first subtracts zeta(0) is not globally injective, and does not satisfy the stated recovery hypothesis. The recovery condition is visible in the theorem statement.

## Reproduction

The original pinned Lean and mathlib versions are retained. Run:

```sh
lake update
lake exe cache get Mogulskii.PathTheorem Mogulskii.InjectiveContraction Mathlib.Data.EReal.Inv
lake build Qlearning
lake env lean VerifyQlearningAxioms.lean
```

The audit follows the sixteen principal declarations transitively and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`. In particular it rejects `sorryAx` and any newly postulated Mogulskii or contraction axiom. The coverage limitations above are theorem hypotheses or unfinished connections, not hidden axioms.
