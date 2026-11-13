# Mogulskii interface for the Q-learning paper

This extension connects the existing finite-dimensional path LDP to the fixed-window argument in Appendix B.1 of *Local Moment Agreement Does Not Preserve Decision Exponents in Coupled Q-Learning*. It does not claim to formalize the whole stationary LDP or the whole paper.

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
| Shared-driver contraction | `controlledWindow_mogulskii` | Proves the LDP for a continuous solution map with a driver-recovery identity. Continuity, existence of that solution map and the identity remain explicit hypotheses. The action is paid once, not separately for the two learners. |
| Real-valued step rescaling | `windowLDP_arbitrary_steps` | Proves the LDP for the canonical reference laws at `n = floor(T/alpha)+1` along any positive vanishing step family, indexed by any filter. It proves the required count divergence and `alpha*n/T -> 1`; it does not identify those reference paths with the actual off-grid recursion. |
| Large individual increments | `maximum_increment_superexponential` | Proves the super-exponential tail for the largest of `n+1` increments from the directional exponential-moment assumptions. |
| Consequence of the Euler estimate | `tracking_implies_superexponential` | Given a deterministic `C/n` times maximum-increment bound, proves exponential equivalence. The deterministic ODE/Euler estimate itself is an input, not assumed to have been formalized. |
| Euler window LDP, conditional on its deterministic estimate | `euler_fixedWindow_LDP` | Combines the tail estimate, exponential-equivalence transfer and physical speed conversion, and returns the good-rate property. |
| Exponential-equivalence transfer | `exponentialBounds_of_equivalent` | Proves transfer of the good rate from exact paths to measurable exponentially equivalent approximations on the integer meshes. |

## Obligations that are still outside this extension

1. Construct the specific Bellman-max solution map and prove its continuity estimate and recovery identity from the integral equation. These are the deterministic results of Lemma B.1.
2. Prove the deterministic Euler tracking estimate for the actual coupled Q-learning recursion, as in Lemma B.2.
3. Prove a pathwise comparison between the actual off-grid noise polygon and the canonical reference polygon, then combine the real-step rescaling with exponential equivalence. A counting/speed rescaling alone does not finish this identification.
4. The stationary tail, sandwich, last-exit argument and stationary limit of Appendix B.2--B.3 are not part of this extension.

The conditional trajectory theorem cannot be described as an unconditional formalization of the full Lemma B.3. The noise theorem, time-scale conversion and tail estimate have only their stated standard probabilistic assumptions.

## Reproduction

The original pinned Lean and mathlib versions are retained. Run:

```sh
lake update
lake exe cache get Mogulskii.PathTheorem Mogulskii.InjectiveContraction Mathlib.Data.EReal.Inv
lake build Qlearning
lake env lean VerifyQlearningAxioms.lean
```

The audit follows the eight principal declarations transitively and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`. In particular it rejects `sorryAx` and any newly postulated Mogulskii or contraction axiom. The coverage limitations above are theorem hypotheses or unfinished connections, not hidden axioms.
