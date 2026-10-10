module
public import QuantitativePaper.VectorMeasureGradientAdaptation
public import QuantitativeFollowup.TransportDeficitTaylor
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! The actual arbitrary-profile vector self-overlap is a continuous,
monotone unit second moment under the genuine fractional disorder tilt.
The cross identity follows from the proved whole-past terminal-spin law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal BigOperators Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorMeanOverlap (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (q : Paper.Overlap) : ℝ :=
  (∑l : Fin n,∫sample,(vectorMeasureSpinMean μ β t ht q sample l)^2
    ∂vectorMeasureDisorderTilt μ β t a)/(n:ℝ)

theorem measurable_vectorMeanOverlap_component (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (l : Fin n) :
    Measurable (fun sample=>vectorMeasureSpinMean μ β t ht q sample l) :=
  (adapted_vectorMeasureSpinMean_component μ β t ht q l).mono
    ((vectorBrownianFiltration n).le _) le_rfl

theorem integrable_vectorMeanOverlap_mul (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (r q : Paper.Overlap) (l : Fin n) :
    Integrable (fun sample=>vectorMeasureSpinMean μ β t ht r sample l*
      vectorMeasureSpinMean μ β t ht q sample l) (vectorMeasureDisorderTilt μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  apply (integrable_const (1:ℝ)).mono'
    ((measurable_vectorMeanOverlap_component μ β t ht r l).mul
      (measurable_vectorMeanOverlap_component μ β t ht q l)).aestronglyMeasurable
  filter_upwards with sample
  change ‖vectorMeasureSpinMean μ β t ht r sample l*vectorMeasureSpinMean μ β t ht q sample l‖≤1
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
  exact (mul_le_mul (vectorMeasureSpinMean_component_bound μ β t ht r sample l)
    (vectorMeasureSpinMean_component_bound μ β t ht q sample l)
    (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem vectorMeanOverlap_cross (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q) (l : Fin n) :
    (∫sample,vectorMeasureSpinMean μ β t ht.le r sample l*
      vectorMeasureSpinMean μ β t ht.le q sample l ∂vectorMeasureDisorderTilt μ β t a)=
      ∫sample,(vectorMeasureSpinMean μ β t ht.le r sample l)^2
        ∂vectorMeasureDisorderTilt μ β t a := by
  have hZ:=adapted_vectorMeasureSpinMean_component μ β t ht.le r l
  have hZq : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal]
      (fun sample=>vectorMeasureSpinMean μ β t ht.le r sample l):=
    hZ.mono ((vectorBrownianFiltration n).mono (Real.toNNReal_mono hrq)) le_rfl
  have hB (sample : VectorDisorderBrownianSample n) :
      ‖vectorMeasureSpinMean μ β t ht.le r sample l‖≤(1:ℝ≥0):=by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using
      vectorMeasureSpinMean_component_bound μ β t ht.le r sample l
  have heq:=vectorMeasure_terminal_spin_pairing_past μ β t a hβ ht q l _ hZq 1 hB
  have her:=vectorMeasure_terminal_spin_pairing_past μ β t a hβ ht r l _ hZ 1 hB
  rw [←heq,her]
  congr 1
  funext sample
  ring

theorem vectorMeanOverlap_component_mono (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q) (l : Fin n) :
    (∫sample,(vectorMeasureSpinMean μ β t ht.le r sample l)^2
      ∂vectorMeasureDisorderTilt μ β t a)≤
    ∫sample,(vectorMeasureSpinMean μ β t ht.le q sample l)^2
      ∂vectorMeasureDisorderTilt μ β t a := by
  let P:=vectorMeasureDisorderTilt (n:=n) μ β t a
  let f:=fun sample=>vectorMeasureSpinMean μ β t ht.le r sample l
  let g:=fun sample=>vectorMeasureSpinMean μ β t ht.le q sample l
  have hff : Integrable (fun sample=>f sample^2) P:=by
    simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht.le r r l
  have hgg : Integrable (fun sample=>g sample^2) P:=by
    simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht.le q q l
  have hfg : Integrable (fun sample=>f sample*g sample) P:=
    integrable_vectorMeanOverlap_mul μ β t a ht.le r q l
  have hh:=integral_mono (hfg.const_mul 2) (hff.add hgg)
    (fun sample=>by simp only [Pi.add_apply];nlinarith [sq_nonneg (f sample-g sample)])
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add hff hgg] at hh
  have he:=vectorMeanOverlap_cross μ β t a hβ ht r q hrq l
  change (∫sample,f sample*g sample∂P)=∫sample,f sample^2∂P at he
  change (∫sample,f sample^2∂P)≤∫sample,g sample^2∂P
  linarith

theorem vectorMeanOverlap_monotone (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) : Monotone (vectorMeanOverlap (n:=n) μ β t a ht.le) := by
  intro r q hrq
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact Finset.sum_le_sum fun l _=>vectorMeanOverlap_component_mono μ β t a hβ ht r q hrq l

theorem vectorMeanOverlap_nonneg_le_one (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    0≤vectorMeanOverlap (n:=n) μ β t a ht q ∧ vectorMeanOverlap (n:=n) μ β t a ht q≤1 := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have hi (l : Fin n) : Integrable (fun sample=>(vectorMeasureSpinMean μ β t ht q sample l)^2)
      (vectorMeasureDisorderTilt μ β t a):=by
    simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht q q l
  have hb (l : Fin n) : (∫sample,(vectorMeasureSpinMean μ β t ht q sample l)^2
      ∂vectorMeasureDisorderTilt μ β t a)≤1 := by
    have hh:=integral_mono (hi l) (integrable_const (1:ℝ)) (fun sample=>by
      have hg:=abs_le.mp (vectorMeasureSpinMean_component_bound μ β t ht q sample l)
      nlinarith)
    simpa only [integral_const,probReal_univ,one_smul] using hh
  refine ⟨div_nonneg (Finset.sum_nonneg fun l _=>integral_nonneg fun sample=>sq_nonneg _)
    (Nat.cast_nonneg n),?_⟩
  unfold vectorMeanOverlap
  calc
    _≤(∑_l : Fin n,(1:ℝ))/(n:ℝ):=div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun l _=>hb l) (Nat.cast_nonneg n)
    _≤1:=by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      exact div_self_le_one _

theorem continuous_vectorMeanOverlap_component (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (sample : VectorDisorderBrownianSample n) (l : Fin n) :
    Continuous (fun q : Paper.Overlap=>vectorMeasureSpinMean μ β t ht q sample l) := by
  have hX:Continuous (fun q : Paper.Overlap=>vectorMeasureState μ β t ht (q:ℝ).toNNReal sample):=
    (continuous_vectorMeasureState μ β t ht sample).comp
      (continuous_real_toNNReal.comp continuous_subtype_val)
  have hz : Continuous (fun q : Paper.Overlap=>
      (q,(sample.1,vectorMeasureState μ β t ht (q:ℝ).toNNReal sample))) :=
    continuous_id.prodMk (continuous_const.prodMk hX)
  have hh := (continuous_vectorMeasureGradient (n:=n) μ β t ht).comp hz
  have hg : Continuous (fun q : Paper.Overlap=>vectorMeasureSpinMean μ β t ht q sample) := by
    change Continuous (fun q : Paper.Overlap=>vectorMeasureGradient μ β t q sample.1
      (vectorMeasureState μ β t ht (q:ℝ).toNNReal sample))
    exact hh
  exact (EuclideanSpace.proj l).continuous.comp hg

theorem continuous_vectorMeanOverlap (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) : Continuous (vectorMeanOverlap (n:=n) μ β t a ht) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  unfold vectorMeanOverlap
  apply Continuous.div_const
  apply continuous_finsetSum
  intro l _
  apply continuous_of_dominated (μ:=vectorMeasureDisorderTilt (n:=n) μ β t a) (bound:=fun _=>(1:ℝ))
  · intro q
    exact ((measurable_vectorMeanOverlap_component μ β t ht q l).pow_const 2).aestronglyMeasurable
  · intro q
    filter_upwards with sample
    rw [norm_pow,Real.norm_eq_abs]
    exact pow_le_one₀ (abs_nonneg _) (vectorMeasureSpinMean_component_bound μ β t ht q sample l)
  · exact integrable_const _
  · exact .of_forall fun sample=>(continuous_vectorMeanOverlap_component μ β t ht sample l).pow 2

end QuantitativeFollowup
