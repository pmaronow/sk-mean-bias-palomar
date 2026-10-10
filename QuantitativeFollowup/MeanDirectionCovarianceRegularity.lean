module
public import QuantitativeFollowup.QuantileWindowCovarianceSplit

@[expose] public section

/-! Measurability and unit bounds of the actual mean-direction covariance.
Its time-dependent conditional covariance is recovered from covariance
decay to the fixed terminal sigma algebra, avoiding any assumed joint
version of the conditional-expectation process. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter QuantitativePaper
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorMeanDirectionCovariance_eq_future (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    vectorMeanDirectionCovariance (n:=n) μ β t a ht.le q=
      (vectorDirectionCovariance (n:=n) μ β t a ht.le (vectorMeasureSpinMean μ β t ht.le q) 1+
        ∫sample : VectorDisorderBrownianSample n,(inner ℝ (vectorMeasureSpinMean μ β t ht.le q sample)
          (vectorMeasureSpinMean μ β t ht.le 1 sample-vectorMeasureSpinMean μ β t ht.le q sample))^2
          ∂vectorMeasureDisorderTilt (n:=n) μ β t a)/(n:ℝ)^2 := by
  let K : ℝ≥0:=⟨Real.sqrt (n:ℝ),Real.sqrt_nonneg _⟩
  have hK (sample : VectorDisorderBrownianSample n) :
      ‖vectorMeasureSpinMean μ β t ht.le q sample‖≤(K:ℝ):=norm_vectorMeasureSpinMean_le μ β t ht.le q sample
  have h:=vectorMeasure_random_covariance_decay μ β t a hβ ht q 1 q.property.2
    (vectorMeasureSpinMean μ β t ht.le q) (adapted_vectorMeasureSpinMean μ β t ht.le q) K hK
  unfold vectorMeanDirectionCovariance vectorDirectionCovariance
  congr 1
  linarith

theorem measurable_vectorMeanDirectionCovariance (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) :
    Measurable (vectorMeanDirectionCovariance (n:=n) μ β t a ht.le) := by
  let :=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  have hM:=measurable_uncurry_vectorMeasureSpinMean (n:=n) μ β t ht.le
  have hC : Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      vectorMeasureCovarianceQuadratic μ β t a ht.le 1 z.2 (vectorMeasureSpinMean μ β t ht.le z.1 z.2)) := by
    unfold vectorMeasureCovarianceQuadratic
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact (((measurable_vectorMeasureSpinCovariance_entry μ β t a ht.le 1 i j).comp measurable_snd).mul
      ((EuclideanSpace.proj i).continuous.measurable.comp hM)).mul
      ((EuclideanSpace.proj j).continuous.measurable.comp hM)
  have hM1 : Measurable (vectorMeasureSpinMean (n:=n) μ β t ht.le 1):=
    (adapted_vectorMeasureSpinMean μ β t ht.le 1).mono ((vectorBrownianFiltration n).le _) le_rfl
  have hD : Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      (inner ℝ (vectorMeasureSpinMean μ β t ht.le z.1 z.2)
        (vectorMeasureSpinMean μ β t ht.le 1 z.2-vectorMeasureSpinMean μ β t ht.le z.1 z.2))^2) :=
    (hM.inner ((hM1.comp measurable_snd).sub hM)).pow_const 2
  have h:=((hC.stronglyMeasurable.integral_prod_right'
    (ν:=vectorMeasureDisorderTilt (n:=n) μ β t a)).measurable.add
    ((hD.stronglyMeasurable.integral_prod_right'
      (ν:=vectorMeasureDisorderTilt (n:=n) μ β t a)).measurable)).div_const ((n:ℝ)^2)
  convert h using 1
  funext q
  exact vectorMeanDirectionCovariance_eq_future μ β t a hβ ht q

theorem vectorMeanDirectionCovariance_nonneg_le_one (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    0≤vectorMeanDirectionCovariance (n:=n) μ β t a ht.le q ∧
      vectorMeanDirectionCovariance (n:=n) μ β t a ht.le q≤1 := by
  let :=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  have hnreal : 0<(n:ℝ):=Nat.cast_pos.mpr hn
  refine ⟨div_nonneg (vectorDirectionCovariance_nonneg μ β t a hβ ht _ q) (sq_nonneg _),?_⟩
  have hb (sample : VectorDisorderBrownianSample n) : ‖vectorMeasureSpinMean μ β t ht.le q sample‖^2≤(n:ℝ):=
    norm_sq_le_dimension_of_components (vectorMeasureSpinMean μ β t ht.le q sample)
      (vectorMeasureSpinMean_component_bound μ β t ht.le q sample)
  have hi : Integrable (fun sample : VectorDisorderBrownianSample n=>‖vectorMeasureSpinMean μ β t ht.le q sample‖^2)
      (vectorMeasureDisorderTilt (n:=n) μ β t a) := by
    have h:= (memLp_vectorMeasureSpinMean (n:=n) μ β t a ht.le q).norm.integrable_mul
      (memLp_vectorMeasureSpinMean (n:=n) μ β t a ht.le q).norm
    change Integrable (fun sample=>‖vectorMeasureSpinMean μ β t ht.le q sample‖*
      ‖vectorMeasureSpinMean μ β t ht.le q sample‖) (vectorMeasureDisorderTilt (n:=n) μ β t a) at h
    simpa only [pow_two] using h
  have he:=integral_mono hi (integrable_const (n:ℝ)) hb
  simp only [integral_const,probReal_univ,one_smul] at he
  have hd:=vectorDirectionCovariance_le_dimension_moment μ β t a hβ ht q _
    (memLp_vectorMeasureSpinMean (n:=n) μ β t a ht.le q)
  have hupper : vectorDirectionCovariance μ β t a ht.le (vectorMeasureSpinMean (n:=n) μ β t ht.le q) q≤(n:ℝ)^2 :=
    hd.trans ((mul_le_mul_of_nonneg_left he hnreal.le).trans_eq (by ring))
  exact (div_le_one₀ (sq_pos_of_pos hnreal)).mpr hupper

theorem integrable_vectorMeanDirectionCovariance (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (hβ : β≠0) (ht : t<1) :
    Integrable (vectorMeanDirectionCovariance (n:=n) μ β t a ht.le) (parisiFreeMeasure μ s) := by
  apply (integrable_const (1:ℝ)).mono'
    (measurable_vectorMeanDirectionCovariance μ β t a hβ ht).aestronglyMeasurable
  exact .of_forall fun q=>by
    rw [Real.norm_of_nonneg (vectorMeanDirectionCovariance_nonneg_le_one hn μ β t a hβ ht q).1]
    exact (vectorMeanDirectionCovariance_nonneg_le_one hn μ β t a hβ ht q).2

end QuantitativeFollowup
