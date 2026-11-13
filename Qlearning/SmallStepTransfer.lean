import Qlearning.SmallStep
import Mathlib.Topology.MetricSpace.Thickening

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace Qlearning

noncomputable def smallWeight (α r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-r / α))

theorem smallWeight_add (α r q : ℝ) :
    smallWeight α (r + q) = smallWeight α r * smallWeight α q := by
  unfold smallWeight
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

theorem smallWeight_eventually_le {ι : Type*} {l : Filter ι} {α : ι → ℝ}
    (ha : ∀ᶠ i in l, 0 < α i) (hzero : Tendsto α l (𝓝 0))
    {q : ℝ} (hq : 0 < q) {c : ℝ≥0∞} (hc : c ≠ 0) :
    ∀ᶠ i in l, smallWeight (α i) q ≤ c := by
  rcases eq_or_ne c ⊤ with rfl | ht
  · exact Eventually.of_forall fun _ => le_top
  have hp : 0 < c.toReal := ENNReal.toReal_pos hc ht
  let B := max 0 (-Real.log c.toReal) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hlim := hzero.eventually (isOpen_Iio.mem_nhds (div_pos hq hB))
  filter_upwards [ha, hlim] with i hai hi
  have hi' : B < q / α i := (lt_div_iff₀ hai).2
    (by simpa only [mul_comm] using (lt_div_iff₀ hB).mp hi)
  have hb : -Real.log c.toReal < B := by dsimp [B]; linarith [le_max_right 0 (-Real.log c.toReal)]
  have he : Real.exp (-q / α i) ≤ c.toReal := by
    rw [← Real.exp_log hp]
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  exact (ENNReal.ofReal_le_ofReal he).trans_eq (ENNReal.ofReal_toReal ht)

/-- Exponential-equivalence transfer at speed 1/alpha along any index filter.
This is the real-step counterpart of the upstream integer-indexed transfer theorem. -/
theorem smallStepLDP_of_equivalent {ι Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {l : Filter ι} {α : ι → ℝ}
    (ha : ∀ᶠ i in l, 0 < α i) (hzero : Tendsto α l (𝓝 0))
    (X Y : ι → Ω → E) (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {I : E → ℝ≥0∞} (hgood : Mogulskii.GoodRate I)
    (hldp : HasSmallStepLDP l α (fun i => μ.map (Y i)) I)
    (herr : ∀ δ : ℝ, 0 < δ → ∀ r : ℝ, ∀ᶠ i in l,
      μ {ω | δ < dist (X i ω) (Y i ω)} ≤ smallWeight (α i) r) :
    HasSmallStepLDP l α (fun i => μ.map (X i)) I := by
  constructor
  · intro F hF r hr
    by_cases hr0 : r < 0
    · filter_upwards [ha] with i hai
      haveI : IsProbabilityMeasure (μ.map (X i)) :=
        Measure.isProbabilityMeasure_map (hX i).aemeasurable
      calc
        _ ≤ 1 := prob_le_one
        _ ≤ _ := ENNReal.one_le_ofReal.mpr (Real.one_le_exp_iff.mpr (div_nonneg (neg_nonneg.mpr hr0.le) hai.le))
    obtain ⟨s, hrs, hs⟩ := EReal.exists_between_coe_real hr
    have hrs' : r < s := EReal.coe_lt_coe_iff.mp hrs
    let q := (r + s) / 2
    have hrq : r < q := by dsimp [q]; linarith
    have hqs : q < s := by dsimp [q]; linarith
    have hs0 : 0 ≤ s := (le_of_not_gt hr0).trans hrs'.le
    have hcoe : (ENNReal.ofReal s : EReal) = (s : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left hs0]
    let K : Set E := {x | I x ≤ ENNReal.ofReal s}
    have hK : IsCompact K := hgood.isCompact_sublevel _ ENNReal.ofReal_ne_top
    have hKF : Disjoint K F := by
      rw [Set.disjoint_left]
      intro x hxK hxF
      have hh := hs.trans_le (iInf₂_le x hxF)
      exact (not_le_of_gt hh) (hcoe ▸ EReal.coe_ennreal_le_coe_ennreal_iff.mpr hxK)
    obtain ⟨δ, hδ, hsep⟩ := hKF.exists_cthickenings hK hF
    have hrate : (q : EReal) < ⨅ x ∈ cthickening δ F, (I x : EReal) := by
      apply (show (q : EReal) < s by exact_mod_cast hqs).trans_le
      rw [← hcoe, ← coe_iInf_rate, EReal.coe_ennreal_le_coe_ennreal_iff]
      refine le_iInf₂ fun x hx => ?_
      have hn : x ∉ K := fun hxK =>
        Set.disjoint_left.mp hsep (self_subset_cthickening K hxK) hx
      exact (lt_of_not_ge hn).le
    have hhalf : ∀ᶠ i in l, smallWeight (α i) (q - r) ≤ ENNReal.ofReal (1 / 2) :=
      smallWeight_eventually_le ha hzero (sub_pos.mpr hrq) (by norm_num)
    filter_upwards [hldp.1 _ isClosed_cthickening q hrate, herr δ hδ q, hhalf]
      with i hi he hiHalf
    rw [Measure.map_apply (hX i) hF.measurableSet]
    rw [Measure.map_apply (hY i) isClosed_cthickening.measurableSet] at hi
    have hsub : X i ⁻¹' F ⊆ Y i ⁻¹' cthickening δ F ∪
        {ω | δ < dist (X i ω) (Y i ω)} := by
      intro ω hω
      by_cases hd : δ < dist (X i ω) (Y i ω)
      · exact Or.inr hd
      · exact Or.inl (mem_cthickening_of_dist_le _ _ _ _ hω
          (by simpa only [dist_comm] using le_of_not_gt hd))
    have hh : smallWeight (α i) (q - r) + smallWeight (α i) (q - r) ≤ 1 := by
      exact (add_le_add hiHalf hiHalf).trans_eq (by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num)
    calc
      _ ≤ μ (Y i ⁻¹' cthickening δ F) + μ {ω | δ < dist (X i ω) (Y i ω)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ smallWeight (α i) q + smallWeight (α i) q := add_le_add hi he
      _ = smallWeight (α i) r *
          (smallWeight (α i) (q - r) + smallWeight (α i) (q - r)) := by
        rw [mul_add, ← smallWeight_add, show r + (q - r) = q by ring]
      _ ≤ smallWeight (α i) r * 1 := mul_le_mul' le_rfl hh
      _ = _ := mul_one _
  · intro U hU r hr
    have hx : ∃ x ∈ U, (I x : EReal) < r := by
      by_contra hn
      exact (not_le_of_gt hr) (le_iInf₂ fun x hx => le_of_not_gt fun hh => hn ⟨x, hx, hh⟩)
    obtain ⟨x, hxU, hx⟩ := hx
    obtain ⟨q, hxq, hqr⟩ := EReal.exists_between_coe_real hx
    have hqr' : q < r := EReal.coe_lt_coe_iff.mp hqr
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
    let δ := ε / 2
    have hδ : 0 < δ := half_pos hε
    have hrate : (⨅ y ∈ ball x δ, (I y : EReal)) < q :=
      (iInf₂_le x (mem_ball_self hδ)).trans_lt hxq
    have hsmall1 := smallWeight_eventually_le ha hzero (by norm_num : (0 : ℝ) < 1)
      (by norm_num : ENNReal.ofReal (1 / 2) ≠ 0)
    have hsmallgap := smallWeight_eventually_le ha hzero (sub_pos.mpr hqr')
      (by norm_num : ENNReal.ofReal (1 / 2) ≠ 0)
    filter_upwards [hldp.2 _ isOpen_ball q hrate, herr δ hδ (q + 1), hsmall1, hsmallgap]
      with i hi he hiSmall hiGap
    rw [Measure.map_apply (hY i) isOpen_ball.measurableSet] at hi
    have hsub : Y i ⁻¹' ball x δ ⊆ X i ⁻¹' ball x ε ∪
        {ω | δ < dist (X i ω) (Y i ω)} := by
      intro ω hω
      by_cases hd : δ < dist (X i ω) (Y i ω)
      · exact Or.inr hd
      · apply Or.inl
        have hy : dist (Y i ω) x < δ := hω
        have ht := dist_triangle (X i ω) (Y i ω) x
        change dist (X i ω) x < ε
        dsimp [δ] at hy hd
        linarith [le_of_not_gt hd]
    let c : ℝ≥0∞ := ENNReal.ofReal (1 / 2)
    have hc : c + c = 1 := by
      dsimp [c]
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    have he' : μ {ω | δ < dist (X i ω) (Y i ω)} ≤ c * smallWeight (α i) q := by
      calc
        _ ≤ smallWeight (α i) (q + 1) := he
        _ = smallWeight (α i) q * smallWeight (α i) 1 := smallWeight_add _ _ _
        _ ≤ smallWeight (α i) q * c := mul_le_mul' le_rfl hiSmall
        _ = _ := mul_comm _ _
    have hsum : c * smallWeight (α i) q + c * smallWeight (α i) q ≤
        μ (X i ⁻¹' ball x ε) + c * smallWeight (α i) q := by
      rw [← add_mul, hc, one_mul]
      exact hi.trans (((measure_mono hsub).trans (measure_union_le _ _)).trans
        (add_le_add le_rfl he'))
    have hfin : c * smallWeight (α i) q ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hlo := (ENNReal.add_le_add_iff_right hfin).mp hsum
    have hweaker : smallWeight (α i) r ≤ c * smallWeight (α i) q := by
      calc
        _ = smallWeight (α i) q * smallWeight (α i) (r - q) := by
          rw [← smallWeight_add, show q + (r - q) = r by ring]
        _ ≤ smallWeight (α i) q * c := mul_le_mul' le_rfl hiGap
        _ = _ := mul_comm _ _
    rw [Measure.map_apply (hX i) hU.measurableSet]
    exact hweaker.trans (hlo.trans (measure_mono (preimage_mono hεU)))

/-- Continuous injective contraction for arbitrary small-step index filters. -/
theorem smallStepLDP_map_injective {ι E F : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [T2Space F] [MeasurableSpace F] [BorelSpace F]
    {l : Filter ι} {α : ι → ℝ} {P : ι → Measure E} {I : E → ℝ≥0∞}
    (hldp : HasSmallStepLDP l α P I) (hgood : Mogulskii.GoodRate I)
    (f : E → F) (hf : Continuous f) (hi : Function.Injective f) :
    HasSmallStepLDP l α (fun i => (P i).map f) (Mogulskii.imageRate f I) ∧
      Mogulskii.GoodRate (Mogulskii.imageRate f I) := by
  have hK (c : ℝ≥0∞) (hc : c ≠ ⊤) :
      IsCompact {y | Mogulskii.imageRate f I y ≤ c} := by
    rw [Mogulskii.imageRate_sublevel hi I hc]
    exact (hgood.isCompact_sublevel c hc).image hf
  have hout : Mogulskii.GoodRate (Mogulskii.imageRate f I) := by
    refine ⟨lowerSemicontinuous_iff_isClosed_preimage.2 fun c => ?_, hK⟩
    by_cases hc : c = ⊤
    · simp [hc]
    · exact (hK c hc).isClosed
  refine ⟨⟨?_, ?_⟩, hout⟩
  · intro A hA r hr
    have hrate : (⨅ y ∈ A, (Mogulskii.imageRate f I y : EReal)) ≤
        ⨅ x ∈ f ⁻¹' A, (I x : EReal) := by
      refine le_iInf₂ fun x hx => ?_
      rw [← Mogulskii.imageRate_apply hi I x]
      exact iInf₂_le (f x) hx
    filter_upwards [hldp.1 _ (hA.preimage hf) r (hr.trans_le hrate)] with i hh
    rwa [Measure.map_apply hf.measurable hA.measurableSet]
  · intro U hU r hr
    have hy : ∃ y ∈ U, (Mogulskii.imageRate f I y : EReal) < r := by
      by_contra hn
      exact (not_le_of_gt hr) (le_iInf₂ fun y hy => le_of_not_gt fun hh => hn ⟨y, hy, hh⟩)
    obtain ⟨y, hyU, hyr⟩ := hy
    have hyrange : y ∈ range f := by
      by_contra hn
      rw [Mogulskii.imageRate_eq_top hn] at hyr
      exact not_lt_of_ge le_top hyr
    obtain ⟨x, rfl⟩ := hyrange
    rw [Mogulskii.imageRate_apply hi] at hyr
    have hrate : (⨅ z ∈ f ⁻¹' U, (I z : EReal)) < r :=
      (iInf₂_le x hyU).trans_lt hyr
    filter_upwards [hldp.2 _ (hU.preimage hf) r hrate] with i hh
    rwa [Measure.map_apply hf.measurable hU.measurableSet]

end Qlearning
