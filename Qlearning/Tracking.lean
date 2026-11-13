import Qlearning.MogulskiiWindow

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Qlearning

open Mogulskii

local instance trackingEuclideanMeasurable {d : ℕ} :
    MeasurableSpace (EuclideanSpace ℝ (Fin d)) := borel _
local instance trackingEuclideanBorel {d : ℕ} : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩

/-- The maximum of O(n) IID increments is superexponentially small on scale n.
All directional exponential moments suffice; bounded and Gaussian noise are covered. -/
theorem maximum_increment_superexponential {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : ∀ k, Measurable (X k)) (hInd : iIndepFun X μ)
    (hId : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hMom : ∀ θ : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp (inner ℝ θ (X 0 ω))) μ)
    {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      μ (⋃ k ∈ Finset.range (n + 1), {ω | (n : ℝ) * δ ≤ ‖X k ω‖}) ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * r))) := by
  let θ := (max 0 r + 3) / δ
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθδ : r + 3 ≤ θ * δ := by
    dsimp [θ]
    rw [div_mul_cancel₀ _ hδ.ne']
    linarith [le_max_right 0 r]
  have hm : Measurable (norm : EuclideanSpace ℝ (Fin d) → ℝ) := continuous_norm.measurable
  have hExp (i : ℕ) : Integrable (fun ω => Real.exp (θ * ‖X i ω‖)) μ :=
    ((hId i).comp ((Real.continuous_exp.comp
      (continuous_const.mul continuous_norm)).measurable)).integrable_iff.mpr
      (integrable_exp_mul_norm_of_inner (hX 0) hMom hθ)
  let c := max 0 (cgf (fun ω => ‖X 0 ω‖) μ θ)
  obtain ⟨N, hN⟩ := exists_nat_gt c
  filter_upwards [eventually_ge_atTop N] with n hn
  have hc : c ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hn)
  have raw := measure_block_union_le (X := fun i ω => ‖X i ω‖)
    (Finset.range (n + 1)) (fun k => {k}) (fun i => hm.comp (hX i))
    (hInd.comp (fun _ => norm) (fun _ => hm)) (fun i => (hId i).comp hm)
    (t := θ) (ε := (n : ℝ) * δ) (b := 1) hθ hExp (by simp)
  simp only [Finset.sum_singleton, Finset.card_range, one_mul] at raw
  have hcard : ((n + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (n : ℝ)) := by
    have hh : ((n + 1 : ℕ) : ℝ) ≤ Real.exp (n : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Real.add_one_le_exp (n : ℝ)
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hh
  have hmul := mul_le_mul_of_nonneg_left hθδ (Nat.cast_nonneg (α := ℝ) n)
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-θ * ((n : ℝ) * δ) + c)) := raw
    _ ≤ ENNReal.ofReal (Real.exp (n : ℝ)) *
        ENNReal.ofReal (Real.exp (-θ * ((n : ℝ) * δ) + c)) := mul_le_mul_left hcard _
    _ = ENNReal.ofReal (Real.exp ((n : ℝ) - θ * ((n : ℝ) * δ) + c)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))

/-- A deterministic C/n times maximum-increment estimate implies exponential equivalence.
The witness formulation is equivalent to using the maximum over this finite range. -/
theorem tracking_implies_superexponential {Ω Y : Type*} [MeasurableSpace Ω]
    [MetricSpace Y] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : ∀ k, Measurable (X k)) (hInd : iIndepFun X μ)
    (hId : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hMom : ∀ θ : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp (inner ℝ θ (X 0 ω))) μ)
    (Euler Exact : ℕ → Ω → Y) {C : ℝ} (hC : 0 < C)
    (htrack : ∀ n ω, ∃ k ∈ Finset.range (n + 1),
      dist (Euler n ω) (Exact n ω) ≤ C / n * ‖X k ω‖)
    {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    ∀ᶠ n : ℕ in atTop, μ {ω | δ < dist (Euler n ω) (Exact n ω)} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * r))) := by
  filter_upwards [maximum_increment_superexponential μ X hX hInd hId hMom
    (δ := δ / C) (div_pos hδ hC) r, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  apply le_trans (measure_mono ?_) hn
  intro ω hω
  obtain ⟨k, hk, hb⟩ := htrack n ω
  apply Set.mem_iUnion₂.mpr
  refine ⟨k, hk, ?_⟩
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hh : δ < C * ‖X k ω‖ / n := by
    calc δ < dist (Euler n ω) (Exact n ω) := hω
         _ ≤ C / n * ‖X k ω‖ := hb
         _ = C * ‖X k ω‖ / n := by ring
  have hh' := (lt_div_iff₀ hnreal).mp hh
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hC).2 (by nlinarith [hh'])

/-- An exponentially equivalent measurable approximation inherits the good rate.
This specializes the proved approximation theorem to a constant approximation family. -/
theorem exponentialBounds_of_equivalent {Ω Y : Type*} [MeasurableSpace Ω]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Euler Exact : ℕ → Ω → Y)
    (hEuler : ∀ n, Measurable (Euler n)) (hExact : ∀ n, Measurable (Exact n))
    {I : Y → ℝ≥0∞} (hI : HasExponentialBounds (fun n => μ.map (Exact n)) I)
    (herr : ∀ δ : ℝ, 0 < δ → ∀ r : ℝ, ∀ᶠ n : ℕ in atTop,
      μ {ω | δ < dist (Euler n ω) (Exact n ω)} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * r)))) :
    HasExponentialBounds (fun n => μ.map (Euler n)) I := by
  exact hasExponentialBounds_of_approximation
    (X := Euler) (Y := fun _ => Exact) (J := fun _ => I) (π := fun _ x => x)
    hEuler (fun _ => hExact) hI.isGood (fun _ _ => hI) (fun _ _ _ => le_rfl)
    (fun _ => tendsto_const_nhds) (fun _ _ _ => le_rfl)
    (fun δ hδ r => Eventually.of_forall fun _ => herr δ hδ r)

/-- The probabilistic part of Lemma B.3 on exact meshes, once the deterministic
Euler estimate of Lemma B.2 has been supplied. -/
theorem euler_fixedWindow_LDP {Ω Y : Type*} [MeasurableSpace Ω]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : ∀ k, Measurable (X k)) (hInd : iIndepFun X μ)
    (hId : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hMom : ∀ θ : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp (inner ℝ θ (X 0 ω))) μ)
    (Euler Exact : ℕ → Ω → Y)
    (hEuler : ∀ n, Measurable (Euler n)) (hExact : ∀ n, Measurable (Exact n))
    {I : Y → ℝ≥0∞} (hI : HasExponentialBounds (fun n => μ.map (Exact n)) I)
    {C T : ℝ} (hC : 0 < C) (hT : 0 < T)
    (htrack : ∀ n ω, ∃ k ∈ Finset.range (n + 1),
      dist (Euler n ω) (Exact n ω) ≤ C / n * ‖X k ω‖) :
    HasWindowLDP T (fun n => μ.map (Euler n)) (fun y => ENNReal.ofReal T * I y) ∧
      GoodRate (fun y => ENNReal.ofReal T * I y) := by
  constructor
  · apply speedNLDP_to_windowLDP _ hT
    apply HasExponentialBounds.hasSpeedNLDP
    apply exponentialBounds_of_equivalent μ Euler Exact hEuler hExact hI
    exact fun δ hδ r =>
      tracking_implies_superexponential μ X hX hInd hId hMom Euler Exact hC htrack hδ r
  · exact goodRate_scale hI.isGood hT

end Qlearning
