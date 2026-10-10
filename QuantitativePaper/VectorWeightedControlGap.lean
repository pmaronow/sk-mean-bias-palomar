module
public import QuantitativePaper.VectorWeightedControlTelescope
public import QuantitativePaper.VectorWeightedSourceBounds
public import QuantitativePaper.VectorControlRepresentation

@[expose] public section

/-! Actual weighted finite-profile control gap, with coefficient-error
bounds derived from genuine initial-filtration weighted Itô verification. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem integral_vectorFiniteControlGap_weighted_eq (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable[vectorBrownianFiltration n 0] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    (∫sample,Z sample*vectorFiniteControlGap s β t μ A sample ∂vectorDisorderBrownianMeasure n)=
      ∫sample,(∫r in Ioc 0 1,Z sample*(vectorFiniteControlSource s β t μ A r sample-
        vectorParisiControlCost ((1-t)*β^2) μ A r sample) ∂nonnegativeLebesgueMeasure)
        ∂vectorDisorderBrownianMeasure n := by
  let c := (1-t)*β^2
  have hZg : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le 0) le_rfl
  have hsrcm := measurable_vectorFiniteControlSource s β t μ A hA
  have hsrcb (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
      ‖vectorFiniteControlSource s β t μ A r sample‖≤(3*|c| *(n : ℝ)).toNNReal := by
    rw [Real.coe_toNNReal _ (by positivity)]
    exact norm_vectorFiniteControlSource_le s β t μ A hA r sample
  have hsrc := integrable_vectorBoundedWeightedTimeIntegral _ hsrcm _ hsrcb Z hZg C hC
  have hEi := (vectorFinite_control_verification s β t hβ ht μ A hA).1.bdd_mul
    hZg.aestronglyMeasurable (Eventually.of_forall hC)
  have hCi := (integrable_vectorParisiControlIntegratedCost c μ A hA).bdd_mul
    hZg.aestronglyMeasurable (Eventually.of_forall hC)
  have he : (fun sample=>Z sample*vectorFiniteControlGap s β t μ A sample)=
      (fun sample=>Z sample*(vectorTerminalPotential n β t sample.1
        (vectorControlledState c μ A 1 sample)-vectorRecursion s β t sample.1 (k+2) 0)-
        Z sample*vectorParisiControlIntegratedCost c μ A sample) := by
    funext sample
    unfold vectorFiniteControlGap
    dsimp only [c]
    ring
  rw [he,integral_sub hEi hCi,vectorFinite_control_weighted_verification s β t hβ ht μ A hA Z hZ C hC]
  refine (integral_sub hsrc hCi).symm.trans ?_
  apply integral_congr_ae
  exact Eventually.of_forall (fun sample=>by
    have hsi : IntegrableOn (fun r=>Z sample*vectorFiniteControlSource s β t μ A r sample)
        (Ioc 0 1) nonnegativeLebesgueMeasure := by
      apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1)
        (C := (C : ℝ)*3*|c| *(n : ℝ))).mono'
        (hsrcm.of_uncurry_right.const_mul (Z sample)).aestronglyMeasurable
      exact Eventually.of_forall (fun r=>by
        change ‖Z sample*vectorFiniteControlSource s β t μ A r sample‖≤_
        rw [norm_mul]
        exact (mul_le_mul (hC sample) (norm_vectorFiniteControlSource_le s β t μ A hA r sample)
          (norm_nonneg _) C.coe_nonneg).trans_eq (by dsimp only [c];ring))
    have hci := (integrableOn_vectorParisiControlCost c μ A hA sample).const_mul (Z sample)
    have heC : Z sample*vectorParisiControlIntegratedCost c μ A sample=
        ∫r in Ioc 0 1,Z sample*vectorParisiControlCost c μ A r sample ∂nonnegativeLebesgueMeasure :=
      (integral_const_mul _ _).symm
    change (∫r in Ioc 0 1,Z sample*vectorFiniteControlSource s β t μ A r sample ∂nonnegativeLebesgueMeasure)-
      Z sample*vectorParisiControlIntegratedCost c μ A sample=_
    rw [heC,←integral_sub hsi hci]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r _
    change Z sample*vectorFiniteControlSource s β t μ A r sample-
      Z sample*vectorParisiControlCost c μ A r sample=
      Z sample*(vectorFiniteControlSource s β t μ A r sample-vectorParisiControlCost c μ A r sample)
    ring)

theorem integral_vectorFiniteControlGap_weighted_le (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable[vectorBrownianFiltration n 0] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) (hZn : ∀sample,0≤Z sample) :
    (∫sample,Z sample*vectorFiniteControlGap s β t μ A sample ∂vectorDisorderBrownianMeasure n)≤
      (C : ℝ)*((1-t)*β^2)/2*(n : ℝ)*Paper.parisiCDFDistance μ (Paper.parisiSchemeMeasure s) := by
  rw [integral_vectorFiniteControlGap_weighted_eq s β t hβ ht μ A hA Z hZ C hC]
  let c := (1-t)*β^2
  let w : ℝ≥0→VectorDisorderBrownianSample n→ℝ := fun r sample=>
    vectorFiniteControlSource s β t μ A r sample-vectorParisiControlCost c μ A r sample
  have hm : Measurable (Function.uncurry w) :=
    (measurable_vectorFiniteControlSource s β t μ A hA).sub (measurable_vectorParisiControlCost c μ A hA)
  let K : ℝ≥0 := ((7/2 : ℝ)*|c| *(n : ℝ)).toNNReal
  have hb (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : ‖w r sample‖≤K := by
    rw [show (K : ℝ)=(7/2 : ℝ)*|c| *(n : ℝ) from Real.coe_toNNReal _ (by positivity)]
    change ‖vectorFiniteControlSource s β t μ A r sample-vectorParisiControlCost c μ A r sample‖≤_
    exact (norm_sub_le _ _).trans (by
      have h1 := norm_vectorFiniteControlSource_le s β t μ A hA r sample
      have h2 := norm_vectorParisiControlCost_le c μ A hA r sample
      dsimp only [c] at h2 ⊢
      linarith)
  let g : ℝ≥0→ℝ := fun r=>c/2*(n : ℝ)*|Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r|
  have hgi : IntegrableOn g (Ioc 0 1) nonnegativeLebesgueMeasure :=
    (integrableOn_nnreal_CDF_abs_sub μ (Paper.parisiSchemeMeasure s)).const_mul (c/2*(n : ℝ))
  have hg : (∫r in Ioc 0 1,g r ∂nonnegativeLebesgueMeasure)=
      c/2*(n : ℝ)*Paper.parisiCDFDistance μ (Paper.parisiSchemeMeasure s) := by
    exact (integral_const_mul _ _).trans (by rw [integral_nnreal_CDF_abs_sub])
  have hZg : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le 0) le_rfl
  have hh := vectorBoundedSource_expected_weighted_integral_le w hm K hb Z hZg C hC hZn g hgi
    (fun r _=>by dsimp only [g,c];positivity)
    (fun r _ sample=>vectorFiniteControlSource_sub_cost_le s β t ht.le μ A r sample)
  rw [hg] at hh
  convert! hh using 1 <;> dsimp only [w,c] <;> ring

theorem tendsto_integral_vectorFiniteControlGap_dyadic_weighted (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Tendsto (fun j=>∫sample,Z sample*vectorFiniteControlGap
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t μ A sample ∂vectorDisorderBrownianMeasure n)
      atTop (𝓝 (∫sample,Z sample*vectorMeasureControlGap μ β t A sample ∂vectorDisorderBrownianMeasure n)) := by
  have hUi := (integrable_vectorMeasureControlGap μ β t hβ ht A hA).bdd_mul
    hZ.aestronglyMeasurable (Eventually.of_forall hC)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlim : Tendsto (fun j : ℕ=>(C : ℝ)*(4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)<1)).const_mul
        ((C : ℝ)*(4*(n : ℝ)*((1-t)*β^2)))
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with j hj
  rw [Real.dist_eq,abs_sub_comm]
  apply lt_of_le_of_lt _ hj
  apply integral_sub_le_uniform_bound hUi
    ((integrable_vectorFiniteControlGap _ β t hβ ht μ A hA).bdd_mul hZ.aestronglyMeasurable (Eventually.of_forall hC))
  intro sample
  rw [←mul_sub,abs_mul,←Real.norm_eq_abs (Z sample)]
  exact (mul_le_mul (hC sample) (vectorMeasureControlGap_dyadic_abs_sub_le μ β t ht.le A j sample)
    (abs_nonneg _) C.coe_nonneg).trans_eq (by ring)

theorem integral_vectorMeasureControlGap_weighted_le_zero (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable[vectorBrownianFiltration n 0] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) (hZn : ∀sample,0≤Z sample) :
    (∫sample,Z sample*vectorMeasureControlGap μ β t A sample ∂vectorDisorderBrownianMeasure n)≤0 := by
  have hZg : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le 0) le_rfl
  have hL := tendsto_integral_vectorFiniteControlGap_dyadic_weighted μ β t hβ ht A hA Z hZg C hC
  have hD := ((Paper.tendsto_parisiCDFDistance_grid μ).comp tendsto_vectorDyadicIndex).const_mul
    ((C : ℝ)*((1-t)*β^2)/2*(n : ℝ))
  simp only [mul_zero] at hD
  apply le_of_tendsto_of_tendsto hL hD
  exact Eventually.of_forall (fun j=>by
    have hh := integral_vectorFiniteControlGap_weighted_le (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      β t hβ ht μ A hA Z hZ C hC hZn
    simpa only [FRSB.parisiSchemeMeasure_grid_eq,Function.comp_def] using hh)

end QuantitativePaper
