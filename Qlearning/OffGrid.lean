import Qlearning.SmallStepTransfer
import Qlearning.Tracking

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology BigOperators

namespace Qlearning

open Mogulskii

theorem sum_ramp_eq {n : ℕ} (hn : 0 < n) (t : UnitTime) :
    ∑ i ∈ Finset.range n, ramp n i (t : ℝ) = (n : ℝ) * t := by
  have h := polygon_eq_interpolate (fun _ (_ : Unit) => (1 : ℝ)) n () t
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [polygon, interpolate, partialSum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    smul_eq_mul, mul_one] at h
  change (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, ramp n i (t : ℝ)) = _ at h
  have h' : (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, ramp n i (t : ℝ)) = (t : ℝ) := by
    calc
      _ = (n : ℝ)⁻¹ * ((n : ℝ) * t) := by convert h using 1 <;> ring
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  have h'' := congrArg (fun x : ℝ => (n : ℝ) * x) h'
  simpa only [← mul_assoc, mul_inv_cancel₀ hn0, one_mul] using h''

theorem polygon_time_dist_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (hn : 0 < n) (x : ℕ → E) {M : ℝ}
    (hbound : ∀ i < n, ‖x i‖ ≤ M) (s t : UnitTime) (hst : s ≤ t) :
    dist (polygon n x t) (polygon n x s) ≤ M * ((t : ℝ) - s) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [dist_eq_norm]
  change ‖(n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, ramp n i (t : ℝ) • x i) -
    (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, ramp n i (s : ℝ) • x i)‖ ≤ _
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ‖(ramp n i (t : ℝ) - ramp n i (s : ℝ)) • x i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        (ramp n i (t : ℝ) - ramp n i (s : ℝ)) * M := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      have hd : 0 ≤ ramp n i (t : ℝ) - ramp n i (s : ℝ) :=
        sub_nonneg.mpr (ramp_mono n i hst)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_left (hbound i (Finset.mem_range.mp hi)) hd
    _ = M * ((t : ℝ) - s) := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, sum_ramp_eq hn, sum_ramp_eq hn]
      field_simp <;> ring

theorem norm_polygon_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (hn : 0 < n) (x : ℕ → E) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i < n, ‖x i‖ ≤ M) (t : UnitTime) : ‖polygon n x t‖ ≤ M := by
  have h := polygon_time_dist_le hn x hbound ⟨0, by norm_num⟩ t t.property.1
  rw [polygon_zero, dist_zero_right, sub_zero] at h
  exact h.trans (mul_le_of_le_one_right hM t.property.2)

def unitRescale (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) : C(UnitTime, UnitTime) where
  toFun s := ⟨ρ * (s : ℝ), mul_nonneg hρ0 s.property.1,
    (mul_le_mul_of_nonneg_left s.property.2 hρ0).trans (by simpa only [mul_one] using hρ1)⟩
  continuous_toFun := by fun_prop

noncomputable def warpPath {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S T : ℝ) (hS : 0 < S) (hT : 0 ≤ T) (hTS : T ≤ S)
    (φ : C(UnitTime, E)) : C(UnitTime, E) :=
  S • φ.comp (unitRescale (T / S) (div_nonneg hT hS.le) ((div_le_one hS).mpr hTS))

theorem warp_polygon_dist_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (hn : 0 < n) (x : ℕ → E) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i < n, ‖x i‖ ≤ M)
    {S T : ℝ} (hS : 0 < S) (hT : 0 ≤ T) (hTS : T ≤ S) :
    dist (warpPath S T hS hT hTS (polygon n x)) (T • polygon n x) ≤ 2 * (S - T) * M := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  let u := unitRescale (T / S) (div_nonneg hT hS.le) ((div_le_one hS).mpr hTS) t
  have hu : (u : ℝ) = T / S * (t : ℝ) := rfl
  have hut : u ≤ t := by
    change T / S * (t : ℝ) ≤ (t : ℝ)
    exact mul_le_of_le_one_left t.property.1 ((div_le_one hS).mpr hTS)
  have hd := polygon_time_dist_le hn x hbound u t hut
  have hp := norm_polygon_le hn x hM hbound t
  have hdiff : 0 ≤ S - T := sub_nonneg.mpr hTS
  change dist (S • polygon n x u) (T • polygon n x t) ≤ _
  calc
    _ ≤ dist (S • polygon n x u) (S • polygon n x t) +
        dist (S • polygon n x t) (T • polygon n x t) := dist_triangle _ _ _
    _ = S * dist (polygon n x t) (polygon n x u) + (S - T) * ‖polygon n x t‖ := by
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hS]
      rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff]
      rw [← dist_eq_norm, dist_comm]
    _ ≤ S * (M * ((t : ℝ) - u)) + (S - T) * M :=
      add_le_add (mul_le_mul_of_nonneg_left hd hS.le)
        (mul_le_mul_of_nonneg_left hp hdiff)
    _ = (S - T) * M * (t : ℝ) + (S - T) * M := by
      rw [hu]
      field_simp <;> ring
    _ ≤ _ := by nlinarith [mul_nonneg hdiff hM, t.property.2]

noncomputable def offGridNoise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T α : ℝ) (hT : 0 < T) (ha : 0 < α) (x : ℕ → E) : C(UnitTime, E) :=
  warpPath (α * (windowCount T α : ℝ)) T
    (hT.trans_le (windowCount_bounds hT.le ha).1) hT.le (windowCount_bounds hT.le ha).1
    (polygon (windowCount T α) x)

/-- This is the actual alpha-grid polygon at physical time T*s, not a reference process. -/
theorem offGridNoise_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T α : ℝ) (hT : 0 < T) (ha : 0 < α) (x : ℕ → E) (s : UnitTime) :
    offGridNoise T α hT ha x s =
      α • ((∑ j ∈ Finset.range ⌊T * (s : ℝ) / α⌋₊, x j) +
        (T * (s : ℝ) / α - (⌊T * (s : ℝ) / α⌋₊ : ℝ)) • x ⌊T * (s : ℝ) / α⌋₊) := by
  let n := windowCount T α
  let S := α * (n : ℝ)
  have hn : 0 < n := by dsimp [n, windowCount]; omega
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hS : 0 < S := hT.trans_le (windowCount_bounds hT.le ha).1
  let u := unitRescale (T / S) (div_nonneg hT.le hS.le)
    ((div_le_one hS).mpr (windowCount_bounds hT.le ha).1) s
  have htime : (n : ℝ) * (u : ℝ) = T * (s : ℝ) / α := by
    change (n : ℝ) * (T / (α * (n : ℝ)) * (s : ℝ)) = _
    field_simp <;> ring
  have hscale : S * (n : ℝ)⁻¹ = α := by dsimp [S]; field_simp
  change S • polygon n x u = _
  rw [polygon_eq_interpolate (fun i (_ : Unit) => x i) n () u]
  simp only [interpolate, htime, partialSum]
  rw [smul_smul, hscale]

theorem offGridNoise_distance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T α : ℝ) (hT : 0 < T) (ha : 0 < α) (x : ℕ → E) :
    ∃ k ∈ Finset.range (windowCount T α + 1),
      dist (offGridNoise T α hT ha x) (T • polygon (windowCount T α) x) ≤ 2 * α * ‖x k‖ := by
  let n := windowCount T α
  have hn : 0 < n := by dsimp [n, windowCount]; omega
  obtain ⟨k, hk, hmax⟩ := (Finset.range (n + 1)).exists_max_image (fun j => ‖x j‖) (by simp)
  have hb : ∀ i < n, ‖x i‖ ≤ ‖x k‖ := fun i hi =>
    hmax i (Finset.mem_range.mpr (Nat.lt_succ_of_lt hi))
  have h := warp_polygon_dist_le hn x (norm_nonneg _) hb
    (hT.trans_le (windowCount_bounds hT.le ha).1) hT.le (windowCount_bounds hT.le ha).1
  refine ⟨k, hk, h.trans ?_⟩
  have hupper := (windowCount_bounds hT.le ha).2
  nlinarith [mul_le_mul_of_nonneg_right hupper (norm_nonneg (x k))]

local instance offGridEuclideanMeasurable {d : ℕ} :
    MeasurableSpace (EuclideanSpace ℝ (Fin d)) := borel _
local instance offGridEuclideanBorel {d : ℕ} : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
local instance offGridPathMeasurable {d : ℕ} : MeasurableSpace (WalkPath d) := borel _
local instance offGridPathBorel {d : ℕ} : BorelSpace (WalkPath d) := ⟨rfl⟩

theorem measurable_offGridNoise {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : ∀ k, Measurable (X k))
    (T α : ℝ) (hT : 0 < T) (ha : 0 < α) :
    Measurable (fun ω => offGridNoise T α hT ha (fun j => X j ω)) := by
  let n := windowCount T α
  let S := α * (n : ℝ)
  have hS : 0 < S := hT.trans_le (windowCount_bounds hT.le ha).1
  let u := unitRescale (T / S) (div_nonneg hT.le hS.le)
    ((div_le_one hS).mpr (windowCount_bounds hT.le ha).1)
  have hw : Continuous (fun φ : WalkPath d => S • φ.comp u) :=
    (ContinuousMap.continuous_precomp u).const_smul S
  exact hw.measurable.comp ((continuous_polygon n).measurable.comp (measurable_pi_lambda _ hX))

/-- The maximum-increment estimate in the paper's actual 1/alpha speed. -/
theorem maximum_increment_smallStep {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : ∀ k, Measurable (X k)) (hInd : iIndepFun X μ)
    (hId : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hMom : ∀ θ : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp (inner ℝ θ (X 0 ω))) μ)
    {T : ℝ} (hT : 0 < T) {l : Filter ι} {α : ι → ℝ}
    (ha : ∀ᶠ i in l, 0 < α i) (hzero : Tendsto α l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    ∀ᶠ i in l, μ (⋃ k ∈ Finset.range (windowCount T (α i) + 1),
      {ω | ε ≤ α i * ‖X k ω‖}) ≤ smallWeight (α i) r := by
  let q := (max 0 r + 1) / T
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hTq : r ≤ T * q := by
    dsimp [q]
    rw [mul_div_cancel₀ _ hT.ne']
    linarith [le_max_right 0 r]
  have htail := (windowCount_tendsto hT ha hzero).eventually
    (maximum_increment_superexponential μ X hX hInd hId hMom
      (δ := ε / (2 * T)) (by positivity) q)
  have hsmall := hzero.eventually (isOpen_Iio.mem_nhds hT)
  filter_upwards [ha, hsmall, htail] with i hai his hi
  let n := windowCount T (α i)
  have hb : α i * (n : ℝ) ≤ 2 * T := by
    have h := (windowCount_bounds hT.le hai).2
    dsimp [n]
    linarith
  have hsub : (⋃ k ∈ Finset.range (n + 1), {ω | ε ≤ α i * ‖X k ω‖}) ⊆
      ⋃ k ∈ Finset.range (n + 1), {ω | (n : ℝ) * (ε / (2 * T)) ≤ ‖X k ω‖} := by
    intro ω hω
    obtain ⟨k, hk, hval⟩ := Set.mem_iUnion₂.mp hω
    refine Set.mem_iUnion₂.mpr ⟨k, hk, ?_⟩
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2 * T)).2
    have h1 := mul_le_mul_of_nonneg_left hval (Nat.cast_nonneg (α := ℝ) n)
    have h2 := mul_le_mul_of_nonneg_right hb (norm_nonneg (X k ω))
    nlinarith
  apply ((measure_mono hsub).trans hi).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hnq : r ≤ α i * (n : ℝ) * q :=
    hTq.trans (mul_le_mul_of_nonneg_right (windowCount_bounds hT.le hai).1 hq)
  have hh : r / α i ≤ (n : ℝ) * q :=
    (div_le_iff₀ hai).2 (by nlinarith [hnq])
  simpa only [smallWeight, neg_div] using neg_le_neg hh

/-- Mogulskii for the actual alpha-grid noise process on [0,T], along every
positive vanishing step family. No off-grid comparison is left as a hypothesis. -/
theorem iid_offGrid_smallStep_mogulskii {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : ∀ k, Measurable (X k)) (hInd : iIndepFun X μ)
    (hId : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hMom : ∀ θ : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp (inner ℝ θ (X 0 ω))) μ)
    {T : ℝ} (hT : 0 < T) {l : Filter ι} {α : ι → ℝ}
    (ha : ∀ i, 0 < α i) (hzero : Tendsto α l (𝓝 0)) :
    HasSmallStepLDP l α (fun i => μ.map
      (fun ω => offGridNoise T (α i) hT (ha i) (fun j => X j ω)))
      (windowAction μ (X 0) T) ∧ GoodRate (windowAction μ (X 0) T) := by
  obtain ⟨paths, hm, heq, href, hgood⟩ :=
    iid_canonical_smallStep_mogulskii μ d X hX hInd hId hMom hT
      (Eventually.of_forall ha) hzero
  have heqPaths (n : ℕ) : paths n = fun ω => T • polygon n (fun j => X j ω) := by
    funext ω
    apply ContinuousMap.ext
    intro t
    change paths n ω t = T • polygon n (fun j => X j ω) t
    rw [heq, polygon_eq_interpolate X n ω t]
  let Canon : ι → Ω → WalkPath d :=
    fun i ω => T • polygon (windowCount T (α i)) (fun j => X j ω)
  let Actual : ι → Ω → WalkPath d :=
    fun i ω => offGridNoise T (α i) hT (ha i) (fun j => X j ω)
  have hCanon : HasSmallStepLDP l α (fun i => μ.map (Canon i))
      (windowAction μ (X 0) T) := by
    simpa only [heqPaths, Canon] using href
  have hCanonMeas (i) : Measurable (Canon i) := by
    have hs : Continuous (fun φ : WalkPath d => T • φ) := continuous_id.const_smul T
    exact hs.measurable.comp ((continuous_polygon (windowCount T (α i))).measurable.comp
      (measurable_pi_lambda _ hX))
  have hActualMeas (i) : Measurable (Actual i) :=
    measurable_offGridNoise X hX T (α i) hT (ha i)
  refine ⟨smallStepLDP_of_equivalent μ (Eventually.of_forall ha) hzero Actual Canon
    hActualMeas hCanonMeas hgood hCanon ?_, hgood⟩
  intro δ hδ r
  filter_upwards [maximum_increment_smallStep μ X hX hInd hId hMom hT
    (Eventually.of_forall ha) hzero (half_pos hδ) r] with i hi
  apply (measure_mono ?_).trans hi
  intro ω hω
  obtain ⟨k, hk, hb⟩ := offGridNoise_distance T (α i) hT (ha i) (fun j => X j ω)
  refine Set.mem_iUnion₂.mpr ⟨k, hk, ?_⟩
  have hh : δ < dist (offGridNoise T (α i) hT (ha i) (fun j => X j ω))
      (T • polygon (windowCount T (α i)) (fun j => X j ω)) := hω
  change δ / 2 ≤ α i * ‖X k ω‖
  nlinarith [hh.trans_le hb]

/-- The probability part of the controlled-window LDP for arbitrary small steps.
Only the deterministic solution-map continuity and recovery identity remain inputs. -/
theorem controlled_smallStep_mogulskii {Ω ι Y : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : ∀ k, Measurable (X k)) (hInd : iIndepFun X μ)
    (hId : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hMom : ∀ θ : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp (inner ℝ θ (X 0 ω))) μ)
    {T : ℝ} (hT : 0 < T) {l : Filter ι} {α : ι → ℝ}
    (ha : ∀ i, 0 < α i) (hzero : Tendsto α l (𝓝 0))
    (Ψ : WalkPath d → Y) (hΨ : Continuous Ψ)
    (recover : Y → WalkPath d) (hrec : ∀ ζ, recover (Ψ ζ) = ζ) :
    HasSmallStepLDP l α (fun i => μ.map
      (fun ω => Ψ (offGridNoise T (α i) hT (ha i) (fun j => X j ω))))
      (imageRate Ψ (windowAction μ (X 0) T)) ∧
      GoodRate (imageRate Ψ (windowAction μ (X 0) T)) := by
  have hnoise := iid_offGrid_smallStep_mogulskii μ d X hX hInd hId hMom hT ha hzero
  have hout := smallStepLDP_map_injective hnoise.1 hnoise.2 Ψ hΨ
    (solutionMap_injective_of_driver_recovery hrec)
  simpa only [HasSmallStepLDP, Function.comp_def, Measure.map_map hΨ.measurable
    (measurable_offGridNoise X hX T (α _) hT (ha _))] using hout

/-- The actual-step analogue of the integer-mesh tracking transfer. -/
theorem euler_smallStep_transfer {Ω ι Y : Type*} [MeasurableSpace Ω]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : ∀ k, Measurable (X k)) (hInd : iIndepFun X μ)
    (hId : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hMom : ∀ θ : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp (inner ℝ θ (X 0 ω))) μ)
    {T : ℝ} (hT : 0 < T) {l : Filter ι} {α : ι → ℝ}
    (ha : ∀ i, 0 < α i) (hzero : Tendsto α l (𝓝 0))
    (Euler Exact : ι → Ω → Y) (hEuler : ∀ i, Measurable (Euler i))
    (hExact : ∀ i, Measurable (Exact i)) {I : Y → ℝ≥0∞}
    (hgood : GoodRate I) (hldp : HasSmallStepLDP l α (fun i => μ.map (Exact i)) I)
    {C : ℝ} (hC : 0 < C)
    (htrack : ∀ᶠ i in l, ∀ ω, ∃ k ∈ Finset.range (windowCount T (α i) + 1),
      dist (Euler i ω) (Exact i ω) ≤ C * α i * ‖X k ω‖) :
    HasSmallStepLDP l α (fun i => μ.map (Euler i)) I ∧ GoodRate I := by
  refine ⟨smallStepLDP_of_equivalent μ (Eventually.of_forall ha) hzero
    Euler Exact hEuler hExact hgood hldp ?_, hgood⟩
  intro δ hδ r
  filter_upwards [maximum_increment_smallStep μ X hX hInd hId hMom hT
    (Eventually.of_forall ha) hzero (div_pos hδ hC) r, htrack] with i hi ht
  apply (measure_mono ?_).trans hi
  intro ω hω
  obtain ⟨k, hk, hb⟩ := ht ω
  refine Set.mem_iUnion₂.mpr ⟨k, hk, ?_⟩
  change δ / C ≤ α i * ‖X k ω‖
  apply (div_le_iff₀ hC).2
  have hh : δ < dist (Euler i ω) (Exact i ω) := hω
  nlinarith [hh.trans_le hb]

/-- Appendix B.1's probabilistic window theorem, with its deterministic inputs visible.
Mogulskii, real-step/off-grid identification, contraction, good rates and exponential
equivalence are proved. The concrete Bellman ODE and Euler estimates are not axiomatized:
they are ordinary hypotheses that an application must supply. -/
theorem windowLDP_of_deterministic_estimates {Ω ι Y : Type*} [MeasurableSpace Ω]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : ∀ k, Measurable (X k)) (hInd : iIndepFun X μ)
    (hId : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hMom : ∀ θ : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp (inner ℝ θ (X 0 ω))) μ)
    {T : ℝ} (hT : 0 < T) {l : Filter ι} {α : ι → ℝ}
    (ha : ∀ i, 0 < α i) (hzero : Tendsto α l (𝓝 0))
    (Ψ : WalkPath d → Y) (hΨ : Continuous Ψ)
    (recover : Y → WalkPath d) (hrec : ∀ ζ, recover (Ψ ζ) = ζ)
    (Euler : ι → Ω → Y) (hEuler : ∀ i, Measurable (Euler i))
    {C : ℝ} (hC : 0 < C)
    (htrack : ∀ᶠ i in l, ∀ ω, ∃ k ∈ Finset.range (windowCount T (α i) + 1),
      dist (Euler i ω) (Ψ (offGridNoise T (α i) hT (ha i) (fun j => X j ω))) ≤
        C * α i * ‖X k ω‖) :
    HasSmallStepLDP l α (fun i => μ.map (Euler i))
      (imageRate Ψ (windowAction μ (X 0) T)) ∧
      GoodRate (imageRate Ψ (windowAction μ (X 0) T)) := by
  have hc := controlled_smallStep_mogulskii μ d X hX hInd hId hMom hT ha hzero Ψ hΨ recover hrec
  exact euler_smallStep_transfer μ X hX hInd hId hMom hT ha hzero Euler
    (fun i ω => Ψ (offGridNoise T (α i) hT (ha i) (fun j => X j ω))) hEuler
    (fun i => hΨ.measurable.comp (measurable_offGridNoise X hX T (α i) hT (ha i)))
    hc.2 hc.1 hC htrack

end Qlearning
