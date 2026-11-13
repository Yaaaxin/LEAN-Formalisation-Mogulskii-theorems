import Mogulskii.PathTheorem
import Mogulskii.InjectiveContraction
import Mathlib.Data.EReal.Inv

/-!
# Fixed-window Mogulskii interface for coupled Q-learning

The interval is represented by normalized time `s in [0,1]`; physical time is
`t = T*s`. The noise path at mesh `alpha = T/n` is `T * polygon n X`.
The physical speed is `n/T` and the physical action is `T` times the unit-time
action of the normalized driver. Continuous controlled-solution maps and their
driver-recovery identities are explicit hypotheses, not new axioms.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace Qlearning

open Mogulskii

theorem coe_iInf_rate {E : Type*} (I : E → ℝ≥0∞) (A : Set E) :
    ((⨅ x ∈ A, I x : ℝ≥0∞) : EReal) = ⨅ x ∈ A, (I x : EReal) := by
  apply le_antisymm
  · exact le_iInf₂ fun x hx => EReal.coe_ennreal_le_coe_ennreal_iff.mpr (iInf₂_le x hx)
  · have hnonneg : (0 : EReal) ≤ ⨅ x ∈ A, (I x : EReal) :=
      le_iInf₂ fun x _ => EReal.coe_ennreal_nonneg (I x)
    rw [← EReal.coe_toENNReal hnonneg, EReal.coe_ennreal_le_coe_ennreal_iff]
    refine le_iInf₂ fun x hx => ?_
    simpa only [EReal.toENNReal_coe] using
      EReal.toENNReal_le_toENNReal
        (iInf₂_le x hx : (⨅ y ∈ A, (I y : EReal)) ≤ (I x : EReal))

/-- An interface conversion; no additional probabilistic assumption is added. -/
theorem speedNLDP_to_exponentialBounds {E : Type*}
    [TopologicalSpace E] [MeasurableSpace E]
    {P : ℕ → Measure E} {I : E → ℝ≥0∞}
    (h : HasSpeedNLDP P I) (hgood : GoodRate I) : HasExponentialBounds P I := by
  refine ⟨hgood, ?_, ?_⟩
  · intro F hF r hr
    rw [coe_iInf_rate] at hr
    exact ⟨1, by simp, (h.1 F hF r hr).mono fun n hn => by simpa using hn⟩
  · intro x U hU r hr
    obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 hU
    have hi : (⨅ y ∈ V, (I y : EReal)) < r := (iInf₂_le x hxV).trans_lt hr
    refine ⟨1, by simp, (h.2 V hV r hi).mono fun n hn => ?_⟩
    simpa using hn.trans (measure_mono hVU)

/-- Physical-window LDP bounds, with speed `n/T`, written without logarithms of zero. -/
def HasWindowLDP {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (T : ℝ) (P : ℕ → Measure E) (A : E → ℝ≥0∞) : Prop :=
  (∀ F : Set E, IsClosed F → ∀ r : ℝ, (r : EReal) <
      ⨅ x ∈ F, (A x : EReal) →
    ∀ᶠ n : ℕ in atTop, P n F ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) / T) * r))) ∧
  (∀ U : Set E, IsOpen U → ∀ r : ℝ, (⨅ x ∈ U, (A x : EReal)) <
      (r : EReal) →
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-((n : ℝ) / T) * r)) ≤ P n U)

theorem coe_scaledRate_inf {E : Type*} (I : E → ℝ≥0∞) (A : Set E)
    {T : ℝ} (hT : 0 < T) :
    (⨅ x ∈ A, ((ENNReal.ofReal T * I x : ℝ≥0∞) : EReal)) =
      (T : EReal) * (⨅ x ∈ A, (I x : EReal)) := by
  rw [← coe_iInf_rate]
  simp_rw [← ENNReal.mul_iInf_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hT)) ENNReal.ofReal_ne_top]
  rw [EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left hT.le,
    coe_iInf_rate]

/-- A finite positive change of the action preserves its compact sublevel sets. -/
theorem goodRate_scale {E : Type*} [TopologicalSpace E] [T2Space E]
    {I : E → ℝ≥0∞} (hI : GoodRate I) {T : ℝ} (hT : 0 < T) :
    GoodRate (fun x => ENNReal.ofReal T * I x) := by
  let a := ENNReal.ofReal T
  have ha0 : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hT)
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hset (r : ℝ≥0∞) : {x | a * I x ≤ r} = {x | I x ≤ a⁻¹ * r} := by
    ext x
    change (a * I x ≤ r) ↔ (I x ≤ a⁻¹ * r)
    constructor
    · intro hx
      have hm := mul_le_mul' (le_refl a⁻¹) hx
      simpa only [← mul_assoc, ENNReal.inv_mul_cancel ha0 hat, one_mul] using hm
    · intro hx
      have hm := mul_le_mul' (le_refl a) hx
      simpa only [← mul_assoc, ENNReal.mul_inv_cancel ha0 hat, one_mul] using hm
  have hK (r : ℝ≥0∞) (hr : r ≠ ⊤) : IsCompact {x | a * I x ≤ r} := by
    rw [hset]
    exact hI.isCompact_sublevel _ (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ha0) hr)
  refine ⟨lowerSemicontinuous_iff_isClosed_preimage.2 fun r => ?_, hK⟩
  by_cases hr : r = ⊤
  · simp [hr]
  · exact (hK r hr).isClosed

/-- This is the time-scale conversion used in Appendix B.1: the action gains `T`. -/
theorem speedNLDP_to_windowLDP {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    {P : ℕ → Measure E} {I : E → ℝ≥0∞} (h : HasSpeedNLDP P I)
    {T : ℝ} (hT : 0 < T) :
    HasWindowLDP T P (fun x => ENNReal.ofReal T * I x) := by
  constructor
  · intro F hF r hr
    rw [coe_scaledRate_inf I F hT] at hr
    have hdiv : ((r / T : ℝ) : EReal) < ⨅ x ∈ F, (I x : EReal) := by
      rw [EReal.coe_div]
      apply (EReal.div_lt_iff (by exact_mod_cast hT) (by simp)).2
      simpa only [EReal.mul_comm] using hr
    filter_upwards [h.1 F hF (r / T) hdiv] with n hn
    convert hn using 2 <;> congr 1 <;> ring
  · intro U hU r hr
    rw [coe_scaledRate_inf I U hT] at hr
    have hdiv : (⨅ x ∈ U, (I x : EReal)) < ((r / T : ℝ) : EReal) := by
      rw [EReal.coe_div]
      apply (EReal.lt_div_iff (by exact_mod_cast hT) (by simp)).2
      simpa only [EReal.mul_comm] using hr
    filter_upwards [h.2 U hU (r / T) hdiv] with n hn
    convert hn using 2 <;> congr 1 <;> ring

local instance pathMeasurable {d : ℕ} : MeasurableSpace (WalkPath d) := borel _
local instance pathBorel {d : ℕ} : BorelSpace (WalkPath d) := ⟨rfl⟩
local instance euclideanMeasurable {d : ℕ} :
    MeasurableSpace (EuclideanSpace ℝ (Fin d)) := borel _
local instance euclideanBorel {d : ℕ} : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩

/-- The already proved Mogulskii theorem in the good-rate exponential-bound interface. -/
theorem iid_polygon_exponentialBounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : ∀ k, Measurable (X k)) (hInd : iIndepFun X μ)
    (hId : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hMom : ∀ θ : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp (inner ℝ θ (X 0 ω))) μ) :
    ∃ paths : ℕ → Ω → WalkPath d,
      (∀ n, Measurable (paths n)) ∧
      (∀ n ω t, paths n ω t = interpolate X n ω t) ∧
      HasExponentialBounds (fun n => μ.map (paths n)) (pathRate (cramerRate μ (X 0))) := by
  obtain ⟨paths, hm, heq, hldp, hls, hcpt⟩ := pathLargeDeviation μ d X hX hInd hId hMom
  refine ⟨paths, hm, heq, speedNLDP_to_exponentialBounds hldp ⟨hls, ?_⟩⟩
  intro r hr
  simpa only [ENNReal.coe_toNNReal hr] using hcpt r.toNNReal

/-- Amplitude scaling by a nonzero horizon is an injective continuous path map. -/
theorem scale_path_injective {d : ℕ} {T : ℝ} (hT : T ≠ 0) :
    Function.Injective (fun ζ : WalkPath d => T • ζ) := by
  intro ζ η h
  have h' := congrArg (fun p : WalkPath d => T⁻¹ • p) h
  simpa only [smul_smul, inv_mul_cancel₀ hT, one_smul] using h'

theorem scaled_path_rate {d : ℕ} {T : ℝ} (hT : T ≠ 0)
    (I : WalkPath d → ℝ≥0∞) (ζ : WalkPath d) :
    imageRate (fun η : WalkPath d => T • η) I ζ = I (T⁻¹ • ζ) := by
  have heq : T • (T⁻¹ • ζ) = ζ := by rw [smul_smul, mul_inv_cancel₀ hT, one_smul]
  conv_lhs => rw [← heq]
  exact imageRate_apply (scale_path_injective hT) I _

/-- The physical-time action in normalized coordinates. It includes the horizon factor. -/
noncomputable def windowAction {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d)) (T : ℝ)
    (ζ : WalkPath d) : ℝ≥0∞ :=
  ENNReal.ofReal T * pathRate (cramerRate μ X) (T⁻¹ • ζ)

/-- Noise LDP on an arbitrary fixed positive window, on meshes `alpha = T/n`.
Its path is `s ↦ alpha * S_(floor(n*s))` with the usual polygonal interpolation. -/
theorem iid_fixedWindow_mogulskii {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : ∀ k, Measurable (X k)) (hInd : iIndepFun X μ)
    (hId : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hMom : ∀ θ : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp (inner ℝ θ (X 0 ω))) μ)
    {T : ℝ} (hT : 0 < T) :
    ∃ paths : ℕ → Ω → WalkPath d,
      (∀ n, Measurable (paths n)) ∧
      (∀ n ω t, paths n ω t = T • interpolate X n ω t) ∧
      HasWindowLDP T (fun n => μ.map (paths n)) (windowAction μ (X 0) T) ∧
      GoodRate (windowAction μ (X 0) T) := by
  obtain ⟨paths, hm, heq, hb⟩ := iid_polygon_exponentialBounds μ d X hX hInd hId hMom
  let f := fun ζ : WalkPath d => T • ζ
  have hf : Continuous f := continuous_id.const_smul T
  have hg := hb.map_injective hf (scale_path_injective hT.ne')
  have hw := speedNLDP_to_windowLDP hg.hasSpeedNLDP hT
  refine ⟨(fun n ω => f (paths n ω)), (fun n => hf.measurable.comp (hm n)), ?_, ?_, ?_⟩
  · intro n ω t
    change T • paths n ω t = _
    rw [heq]
  · simpa only [HasWindowLDP, windowAction, Function.comp_def, f, scaled_path_rate hT.ne', Measure.map_map hf.measurable
      (hm _)] using hw
  · have hg' := goodRate_scale hg.isGood hT
    have heqRate : (fun ζ => ENNReal.ofReal T *
        imageRate f (pathRate (cramerRate μ (X 0))) ζ) = windowAction μ (X 0) T := by
      funext ζ
      simp only [windowAction, f, scaled_path_rate hT.ne']
    rwa [heqRate] at hg'

/-- The additive integral equation determines the driver from the trajectory.
`recover` is its residual, e.g. `Q_1 - Q* - integral (T G(Q_1))` in normalized time. -/
theorem solutionMap_injective_of_driver_recovery {E Y : Type*}
    {Ψ : E → Y} {recover : Y → E} (h : ∀ ζ, recover (Ψ ζ) = ζ) :
    Function.Injective Ψ := by
  intro ζ η heq
  simpa only [h] using congrArg recover heq

/-- Contraction to the paired controlled trajectory. The continuity estimate of Appendix B.1
and the integral-equation residual are hypotheses; existence of an ODE solution is not
silently asserted by this interface. Both learners use one driver and pay one action. -/
theorem controlledWindow_mogulskii {Ω Y : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : ∀ k, Measurable (X k)) (hInd : iIndepFun X μ)
    (hId : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hMom : ∀ θ : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp (inner ℝ θ (X 0 ω))) μ)
    {T : ℝ} (hT : 0 < T) (Ψ : WalkPath d → Y) (hΨ : Continuous Ψ)
    (recover : Y → WalkPath d) (hrec : ∀ ζ, recover (Ψ ζ) = ζ) :
    ∃ paths : ℕ → Ω → WalkPath d,
      (∀ n, Measurable (paths n)) ∧
      (∀ n ω t, paths n ω t = T • interpolate X n ω t) ∧
      HasWindowLDP T (fun n => μ.map (fun ω => Ψ (paths n ω)))
        (fun y => ENNReal.ofReal T *
          imageRate Ψ (fun ζ => pathRate (cramerRate μ (X 0)) (T⁻¹ • ζ)) y) ∧
      GoodRate (fun y => ENNReal.ofReal T *
          imageRate Ψ (fun ζ => pathRate (cramerRate μ (X 0)) (T⁻¹ • ζ)) y) := by
  obtain ⟨paths, hm, heq, hb⟩ := iid_polygon_exponentialBounds μ d X hX hInd hId hMom
  let f := fun ζ : WalkPath d => Ψ (T • ζ)
  have hc : Continuous f := hΨ.comp (continuous_id.const_smul T)
  have hi : Function.Injective f :=
    (solutionMap_injective_of_driver_recovery hrec).comp (scale_path_injective hT.ne')
  have hout := hb.map_injective hc hi
  have hw := speedNLDP_to_windowLDP hout.hasSpeedNLDP hT
  have hrate (y : Y) : imageRate f (pathRate (cramerRate μ (X 0))) y =
      imageRate Ψ (fun ζ => pathRate (cramerRate μ (X 0)) (T⁻¹ • ζ)) y := by
    apply le_antisymm
    · refine le_iInf fun ζ => ?_
      refine iInf_le_of_le ⟨T⁻¹ • ζ.val, ?_⟩ ?_
      · dsimp [f]
        simpa only [smul_smul, mul_inv_cancel₀ hT.ne', one_smul] using ζ.property
      · exact le_rfl
    · refine le_iInf fun ζ => ?_
      refine iInf_le_of_le ⟨T • ζ.val, ζ.property⟩ ?_
      simp only [smul_smul, inv_mul_cancel₀ hT.ne', one_smul, le_refl]
  refine ⟨(fun n ω => T • paths n ω),
    (fun n => (continuous_id.const_smul T).measurable.comp (hm n)), ?_, ?_, ?_⟩
  · intro n ω t
    change T • paths n ω t = _
    rw [heq]
  · simpa only [HasWindowLDP, Function.comp_def, f, hrate, Measure.map_map hc.measurable (hm _)] using hw
  · simpa only [hrate] using goodRate_scale hout.isGood hT

end Qlearning
