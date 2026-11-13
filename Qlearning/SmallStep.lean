import Qlearning.MogulskiiWindow

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Qlearning

local instance smallStepEuclideanMeasurable {d : ℕ} :
    MeasurableSpace (EuclideanSpace ℝ (Fin d)) := borel _
local instance smallStepPathMeasurable {d : ℕ} :
    MeasurableSpace (Mogulskii.WalkPath d) := borel _

/-- LDP at speed `1/alpha`, for an arbitrary index filter. -/
def HasSmallStepLDP {ι E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (l : Filter ι) (α : ι → ℝ) (P : ι → Measure E) (A : E → ℝ≥0∞) : Prop :=
  (∀ F : Set E, IsClosed F → ∀ r : ℝ, (r : EReal) <
      ⨅ x ∈ F, (A x : EReal) →
    ∀ᶠ i in l, P i F ≤ ENNReal.ofReal (Real.exp (-r / α i))) ∧
  (∀ U : Set E, IsOpen U → ∀ r : ℝ, (⨅ x ∈ U, (A x : EReal)) <
      (r : EReal) →
    ∀ᶠ i in l, ENNReal.ofReal (Real.exp (-r / α i)) ≤ P i U)

/-- Reindexing uses the actual ratio `alpha * n / T`, rather than assuming exact meshes.
This is the speed argument needed when alpha varies continuously. -/
theorem windowLDP_reindex {ι E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    {T : ℝ} {P : ℕ → Measure E} {A : E → ℝ≥0∞}
    (h : HasWindowLDP T P A) {l : Filter ι} {α : ι → ℝ} {n : ι → ℕ}
    (hn : Tendsto n l atTop) (ha : ∀ᶠ i in l, 0 < α i)
    (hratio : Tendsto (fun i => α i * (n i : ℝ) / T) l (𝓝 1)) :
    HasSmallStepLDP l α (fun i => P (n i)) A := by
  constructor
  · intro F hF r hr
    obtain ⟨q, hrq, hq⟩ := EReal.exists_between_coe_real hr
    have hrq' : r < q := EReal.coe_lt_coe_iff.mp hrq
    have hlim : Tendsto (fun i => q * (α i * (n i : ℝ) / T)) l (𝓝 q) := by
      simpa only [mul_one] using tendsto_const_nhds.mul hratio
    have hev := hlim.eventually (isOpen_Ioi.mem_nhds hrq')
    filter_upwards [hn.eventually (h.1 F hF q hq), ha, hev] with i hi hai hqi
    apply hi.trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hcomp : r / α i ≤ (n i : ℝ) / T * q :=
      (div_le_iff₀ hai).2 (by
        calc r ≤ q * (α i * (n i : ℝ) / T) := hqi.le
             _ = (n i : ℝ) / T * q * α i := by ring)
    simpa only [neg_mul, neg_div] using neg_le_neg hcomp
  · intro U hU r hr
    obtain ⟨q, hq, hqr⟩ := EReal.exists_between_coe_real hr
    have hqr' : q < r := EReal.coe_lt_coe_iff.mp hqr
    have hlim : Tendsto (fun i => q * (α i * (n i : ℝ) / T)) l (𝓝 q) := by
      simpa only [mul_one] using tendsto_const_nhds.mul hratio
    have hev := hlim.eventually (isOpen_Iio.mem_nhds hqr')
    filter_upwards [hn.eventually (h.2 U hU q hq), ha, hev] with i hi hai hqi
    apply le_trans ?_ hi
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hcomp : (n i : ℝ) / T * q ≤ r / α i :=
      (le_div_iff₀ hai).2 (by
        calc (n i : ℝ) / T * q * α i = q * (α i * (n i : ℝ) / T) := by ring
             _ ≤ r := hqi.le)
    simpa only [neg_mul, neg_div] using neg_le_neg hcomp

/-- The integer number of increments in Appendix B.1. -/
noncomputable def windowCount (T α : ℝ) : ℕ := ⌊T / α⌋₊ + 1

theorem windowCount_bounds {T α : ℝ} (hT : 0 ≤ T) (ha : 0 < α) :
    T ≤ α * (windowCount T α : ℝ) ∧ α * (windowCount T α : ℝ) ≤ T + α := by
  have hdiv : 0 ≤ T / α := div_nonneg hT ha.le
  have hlo := Nat.floor_le hdiv
  have hhi := Nat.lt_floor_add_one (T / α)
  have hlo' : (⌊T / α⌋₊ : ℝ) * α ≤ T := (le_div_iff₀ ha).mp hlo
  have hhi' : T < ((⌊T / α⌋₊ : ℝ) + 1) * α := (div_lt_iff₀ ha).mp hhi
  simp only [windowCount, Nat.cast_add, Nat.cast_one]
  constructor <;> nlinarith

theorem windowCount_tendsto {ι : Type*} {l : Filter ι} {α : ι → ℝ}
    {T : ℝ} (hT : 0 < T) (ha : ∀ᶠ i in l, 0 < α i)
    (hzero : Tendsto α l (𝓝 0)) :
    Tendsto (fun i => windowCount T (α i)) l atTop := by
  refine tendsto_atTop.2 fun N => ?_
  have hsmall := hzero.eventually
    (isOpen_Iio.mem_nhds (show (0 : ℝ) < T / ((N : ℝ) + 1) by positivity))
  filter_upwards [ha, hsmall] with i hai hsi
  by_contra hni
  have hnat : windowCount T (α i) ≤ N := Nat.le_of_lt (Nat.lt_of_not_ge hni)
  have hcast : (windowCount T (α i) : ℝ) ≤ N := by exact_mod_cast hnat
  have hmul := mul_le_mul_of_nonneg_left hcast hai.le
  have hb := (windowCount_bounds hT.le hai).1
  have hs := (lt_div_iff₀ (show (0 : ℝ) < (N : ℝ) + 1 by positivity)).mp hsi
  nlinarith

theorem windowCount_ratio_tendsto {ι : Type*} {l : Filter ι} {α : ι → ℝ}
    {T : ℝ} (hT : 0 < T) (ha : ∀ᶠ i in l, 0 < α i)
    (hzero : Tendsto α l (𝓝 0)) :
    Tendsto (fun i => α i * (windowCount T (α i) : ℝ) / T) l (𝓝 1) := by
  have hlower : ∀ᶠ i in l, (1 : ℝ) ≤ α i * (windowCount T (α i) : ℝ) / T := by
    filter_upwards [ha] with i hai
    exact (le_div_iff₀ hT).2 (by simpa using (windowCount_bounds hT.le hai).1)
  have hupper : ∀ᶠ i in l,
      α i * (windowCount T (α i) : ℝ) / T ≤ 1 + α i / T := by
    filter_upwards [ha] with i hai
    have h := div_le_div_of_nonneg_right (windowCount_bounds hT.le hai).2 hT.le
    simpa only [add_div, div_self hT.ne'] using h
  have hlim : Tendsto (fun i => 1 + α i / T) l (𝓝 1) := by
    simpa only [zero_div, add_zero] using tendsto_const_nhds.add (hzero.div_const T)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hlower hupper

/-- Canonical fixed-window laws have the right LDP along every positive vanishing step.
Identifying an actual off-grid process with these laws additionally needs exponential
equivalence; this statement does not hide that further obligation. -/
theorem windowLDP_arbitrary_steps {ι E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    {T : ℝ} {P : ℕ → Measure E} {A : E → ℝ≥0∞}
    (h : HasWindowLDP T P A) (hT : 0 < T)
    {l : Filter ι} {α : ι → ℝ} (ha : ∀ᶠ i in l, 0 < α i)
    (hzero : Tendsto α l (𝓝 0)) :
    HasSmallStepLDP l α (fun i => P (windowCount T (α i))) A :=
  windowLDP_reindex h (windowCount_tendsto hT ha hzero) ha
    (windowCount_ratio_tendsto hT ha hzero)

/-- End-to-end canonical noise theorem for arbitrary positive vanishing steps.
The reference path uses `T * interpolate X (windowCount T alpha)`; it is not
silently renamed as the actual alpha-mesh polygon. -/
theorem iid_canonical_smallStep_mogulskii {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : ∀ k, Measurable (X k)) (hInd : ProbabilityTheory.iIndepFun X μ)
    (hId : ∀ k, ProbabilityTheory.IdentDistrib (X k) (X 0) μ μ)
    (hMom : ∀ θ : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp (inner ℝ θ (X 0 ω))) μ)
    {T : ℝ} (hT : 0 < T) {l : Filter ι} {α : ι → ℝ}
    (ha : ∀ᶠ i in l, 0 < α i) (hzero : Tendsto α l (𝓝 0)) :
    ∃ paths : ℕ → Ω → Mogulskii.WalkPath d,
      (∀ n, Measurable (paths n)) ∧
      (∀ n ω t, paths n ω t = T • Mogulskii.interpolate X n ω t) ∧
      HasSmallStepLDP l α (fun i => μ.map (paths (windowCount T (α i))))
        (windowAction μ (X 0) T) ∧
      Mogulskii.GoodRate (windowAction μ (X 0) T) := by
  obtain ⟨paths, hm, heq, hw, hgood⟩ := iid_fixedWindow_mogulskii μ d X hX hInd hId hMom hT
  exact ⟨paths, hm, heq, windowLDP_arbitrary_steps hw hT ha hzero, hgood⟩

end Qlearning
