module
public import QuantitativeFollowup.VectorScoreTail
public import QuantitativeFollowup.ParisiFreeQuantileSupport
public import QuantitativePaper.VectorMeanOverlapNorm

@[expose] public section

/-! Literal centered self-overlap moments and their contact/variance
identification along every free quantile, not only almost everywhere. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorCenteredSelfOverlapSecond (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (q : Paper.Overlap) : ℝ :=
  ∫z,vectorCenteredSelfOverlap (n:=n) μ β t ht q z^2 ∂vectorMeasureSpinPathLaw μ β t a ht

theorem norm_vectorCenteredSelfOverlap_le_one (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap)
    (z : VectorDisorderBrownianSample n×Configuration n) :
    ‖vectorCenteredSelfOverlap μ β t ht q z‖≤1 := by
  rw [Real.norm_eq_abs,abs_le]
  have hb:=vectorSelfOverlap_bounds hn μ β t ht q z
  change -1≤vectorSelfOverlap μ β t ht q z-(q:ℝ) ∧
    vectorSelfOverlap μ β t ht q z-(q:ℝ)≤1
  constructor <;> linarith [q.property.1,q.property.2]

theorem vectorCenteredSelfOverlapSecond_bounds (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    0≤vectorCenteredSelfOverlapSecond (n:=n) μ β t a ht q ∧
      vectorCenteredSelfOverlapSecond (n:=n) μ β t a ht q≤1 := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  refine ⟨integral_nonneg fun _=>sq_nonneg _,?_⟩
  have h:=integral_mono (memLp_vectorCenteredSelfOverlap hn μ β t a ht q).integrable_sq
    (integrable_const (1:ℝ)) (fun z=>by
      have hb:=norm_vectorCenteredSelfOverlap_le_one hn μ β t ht q z
      rw [Real.norm_eq_abs] at hb
      simpa only [sq_abs,one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hb)
  simpa only [vectorCenteredSelfOverlapSecond,integral_const,probReal_univ,one_smul] using h

theorem measurable_uncurry_vectorCenteredSelfOverlap (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) :
    Measurable (Function.uncurry (vectorCenteredSelfOverlap (n:=n) μ β t ht)) := by
  apply measurable_uncurry_of_continuous_of_measurable
  · intro z
    exact (((continuous_vectorMeasureSpinMean_path μ β t ht z.1).norm.pow 2).div_const _).sub
      continuous_subtype_val
  · intro q
    exact (measurable_vectorSelfOverlap μ β t ht q).sub measurable_const

theorem measurable_vectorCenteredSelfOverlapSecond (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) :
    Measurable (vectorCenteredSelfOverlapSecond (n:=n) μ β t a ht) := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  exact ((measurable_uncurry_vectorCenteredSelfOverlap μ β t ht).pow_const 2).stronglyMeasurable.integral_prod_right.measurable

theorem integral_vectorSelfOverlap_eq_mean (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    (∫z,vectorSelfOverlap (n:=n) μ β t ht q z ∂vectorMeasureSpinPathLaw μ β t a ht)=
      vectorMeanOverlap (n:=n) μ β t a ht q := by
  have hM : Measurable (vectorMeasureSpinMean (n:=n) μ β t ht q):=
    (adapted_vectorMeasureSpinMean μ β t ht q).mono ((vectorBrownianFiltration n).le _) le_rfl
  unfold vectorSelfOverlap
  rw [integral_div,integral_vectorMeasureSpinPathLaw_sample μ β t a ht _ (hM.norm.pow_const 2),
    integral_vectorMeasureSpinMean_norm_sq_eq_overlap hn μ β t a ht q]
  have hn' : (n:ℝ)≠0:=by positivity
  field_simp

theorem vectorCenteredSelfOverlapSecond_eq_variance_of_contact (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap)
    (hcontact : vectorMeanOverlap (n:=n) μ β t a ht q=(q:ℝ)) :
    vectorCenteredSelfOverlapSecond (n:=n) μ β t a ht q=
      variance (vectorSelfOverlap (n:=n) μ β t ht q) (vectorMeasureSpinPathLaw μ β t a ht) := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hX:=memLp_vectorCenteredSelfOverlap hn μ β t a ht q
  have hiS : Integrable (vectorSelfOverlap (n:=n) μ β t ht q) (vectorMeasureSpinPathLaw μ β t a ht) :=
    (MemLp.of_bound (measurable_vectorSelfOverlap μ β t ht q).aestronglyMeasurable 1
      (.of_forall fun z=>by
        rw [Real.norm_of_nonneg (vectorSelfOverlap_bounds hn μ β t ht q z).1]
        exact (vectorSelfOverlap_bounds hn μ β t ht q z).2) :
      MemLp (vectorSelfOverlap (n:=n) μ β t ht q) 2 (vectorMeasureSpinPathLaw μ β t a ht)).integrable one_le_two
  have he : (∫z,vectorCenteredSelfOverlap (n:=n) μ β t ht q z ∂vectorMeasureSpinPathLaw μ β t a ht)=0 := by
    unfold vectorCenteredSelfOverlap
    rw [integral_sub hiS (integrable_const _),integral_vectorSelfOverlap_eq_mean hn μ β t a ht q,
      integral_const,probReal_univ,one_smul,hcontact,sub_self]
  have hv:=variance_eq_sub hX
  simp only [Pi.pow_apply] at hv
  rw [he] at hv
  simp only [zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] at hv
  unfold vectorCenteredSelfOverlapSecond
  rw [←hv]
  exact variance_sub_const (measurable_vectorSelfOverlap μ β t ht q).aestronglyMeasurable _

theorem vectorCenteredSelfOverlapSecond_free_quantile_variance (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s β t : ℝ) (hβ : β≠0) (ht : t<1)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    {v : ℝ} (hv : v∈Ioo (0:ℝ) (1-s)) :
    vectorCenteredSelfOverlapSecond (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v)=
      variance (vectorSelfOverlap (n:=n) μ β t ht.le (parisiFreeQuantile μ s v))
        (vectorMeasureSpinPathLaw μ β t s ht.le) := by
  apply vectorCenteredSelfOverlapSecond_eq_variance_of_contact hn
  exact (vector_free_support_contact hn μ s ⟨hs.1.le,hs.2⟩ hμ β t s hβ ht hs.1.le hmin
    (parisiFreeQuantile μ s v) (parisiFreeQuantile_mem_support μ s ⟨hs.1.le,hs.2.le⟩ ⟨hv.1,hv.2.le⟩)).2

end QuantitativeFollowup
