module
public import QuantitativePaper.VectorMeasureLoewner
public import QuantitativePaper.VectorMeasureHessianProcess
public import FourPapersCommon.IntegralHilbertReaction

@[expose] public section

/-! The genuine averaged covariance reaction for arbitrary square-integrable
random directions. The common null set in the matrix comparison permits the
direction to vary with the sample; no deterministic-direction substitution is
made inside a separate almost-everywhere assertion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem measurable_vectorMeasureSpinCovariance_entry (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (i j : Fin n) :
    Measurable (fun sample => vectorMeasureSpinCovariance μ β t a ht q sample i j) := by
  exact (stronglyMeasurable_condExp.mono ((vectorBrownianFiltration n).le _)).measurable.sub
    (((adapted_vectorMeasureSpinMean_component μ β t ht q i).mono
      ((vectorBrownianFiltration n).le _) le_rfl).mul
      ((adapted_vectorMeasureSpinMean_component μ β t ht q j).mono
        ((vectorBrownianFiltration n).le _) le_rfl))

theorem vectorMeasureSpinCovariance_entry_bound (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) :
    ∀ᵐ sample ∂vectorMeasureDisorderTilt (n := n) μ β t a, ∀ i j : Fin n,
      |vectorMeasureSpinCovariance μ β t a ht q sample i j| ≤ 2 := by
  let P := vectorMeasureDisorderTilt (n := n) μ β t a
  have := vectorMeasureDisorderTilt_probability (n := n) μ β t a ht
  have he (i j : Fin n) : ∀ᵐ sample ∂P,
      |P[vectorMeasureTerminalObservable μ β t ht
        (fun σ => Paper.spinSign (σ i)*Paper.spinSign (σ j)) |
          vectorBrownianFiltration n (q : ℝ).toNNReal] sample| ≤ 1 := by
    let T := vectorMeasureTerminalObservable μ β t ht
      (fun σ => Paper.spinSign (σ i)*Paper.spinSign (σ j))
    have hT : Integrable T P := integrable_vectorMeasureTerminalObservable μ β t a ht _
    have hb (sample : VectorDisorderBrownianSample n) : |T sample| ≤ 1 := by
      exact terminalMean_bound _ _ 1 (fun σ => by simp [abs_mul])
    have hl := condExp_mono (integrable_const (-1 : ℝ) (μ := P)) hT
      (.of_forall fun sample => (abs_le.mp (hb sample)).1)
      (m := vectorBrownianFiltration n (q : ℝ).toNNReal)
    have hu := condExp_mono hT (integrable_const (1 : ℝ) (μ := P))
      (.of_forall fun sample => (abs_le.mp (hb sample)).2)
      (m := vectorBrownianFiltration n (q : ℝ).toNNReal)
    rw [condExp_const ((vectorBrownianFiltration n).le _)] at hl hu
    filter_upwards [hl, hu] with sample hlow hupp
    exact abs_le.mpr ⟨hlow, hupp⟩
  have hall : ∀ᵐ sample ∂P, ∀ i j : Fin n,
      |P[vectorMeasureTerminalObservable μ β t ht
        (fun σ => Paper.spinSign (σ i)*Paper.spinSign (σ j)) |
          vectorBrownianFiltration n (q : ℝ).toNNReal] sample| ≤ 1 := by
    simp only [ae_all_iff]
    exact he
  filter_upwards [hall] with sample hs
  intro i j
  have hm : |vectorMeasureSpinMean μ β t ht q sample i*
      vectorMeasureSpinMean μ β t ht q sample j| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (vectorMeasureSpinMean_component_bound μ β t ht q sample i)
      (vectorMeasureSpinMean_component_bound μ β t ht q sample j)
      (abs_nonneg _) (by norm_num)).trans (by norm_num)
  exact (abs_sub _ _).trans (by linarith [hs i j])

theorem vectorMeasureCovarianceQuadratic_uniform_bound (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) :
    ∀ᵐ sample ∂vectorMeasureDisorderTilt (n := n) μ β t a, ∀ w : Field n,
      |vectorMeasureCovarianceQuadratic μ β t a ht q sample w| ≤
        2*(n : ℝ)^2*‖w‖^2 := by
  filter_upwards [vectorMeasureSpinCovariance_entry_bound μ β t a ht q] with sample hs
  intro w
  unfold vectorMeasureCovarianceQuadratic
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        |vectorMeasureSpinCovariance μ β t a ht q sample i j*w i*w j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, 2*‖w‖*‖w‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      exact mul_le_mul (mul_le_mul (hs i j) (PiLp.norm_apply_le w i)
        (abs_nonneg _) (by norm_num)) (PiLp.norm_apply_le w j)
        (abs_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))
    _ = _ := by simp [Finset.sum_const, pow_two]; ring

theorem integrable_vectorMeasureRandomCovariance (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (q : Paper.Overlap)
    (b : VectorDisorderBrownianSample n → Field n)
    (hb : MemLp b 2 (vectorMeasureDisorderTilt μ β t a)) :
    Integrable (fun sample => vectorMeasureCovarianceQuadratic μ β t a ht q sample (b sample))
      (vectorMeasureDisorderTilt μ β t a) := by
  have hi := hb.norm.integrable_mul hb.norm
  change Integrable (fun sample => ‖b sample‖*‖b sample‖) _ at hi
  apply (hi.const_mul (2*(n : ℝ)^2)).mono'
  · unfold vectorMeasureCovarianceQuadratic
    have hterm (i j : Fin n) : AEStronglyMeasurable (fun sample =>
        vectorMeasureSpinCovariance μ β t a ht q sample i j * (b sample) i * (b sample) j)
        (vectorMeasureDisorderTilt μ β t a) :=
      (((measurable_vectorMeasureSpinCovariance_entry μ β t a ht q i j).aestronglyMeasurable.mul
        ((EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hb.aestronglyMeasurable)).mul
          ((EuclideanSpace.proj j).continuous.comp_aestronglyMeasurable hb.aestronglyMeasurable))
    have hrow (i : Fin n) := Finset.aestronglyMeasurable_sum Finset.univ (fun j _ => hterm i j)
    simpa only [Finset.sum_fn] using
      Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hrow i)
  · filter_upwards [vectorMeasureCovarianceQuadratic_uniform_bound μ β t a ht q] with sample hs
    simpa only [Real.norm_eq_abs, pow_two, mul_assoc] using hs (b sample)

theorem memLp_vectorMeasureHessian_random_apply (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (q : Paper.Overlap)
    (b : VectorDisorderBrownianSample n → Field n)
    (hb : MemLp b 2 (vectorMeasureDisorderTilt μ β t a)) :
    MemLp (fun sample => vectorMeasureHessianProcess μ β t ht q sample (b sample)) 2
      (vectorMeasureDisorderTilt μ β t a) := by
  have hH : AEStronglyMeasurable (vectorMeasureHessianProcess (n := n) μ β t ht q)
      (vectorMeasureDisorderTilt μ β t a) :=
    ((adapted_vectorMeasureHessianProcess (n := n) μ β t ht q).mono
    ((vectorBrownianFiltration n).le _) le_rfl).aestronglyMeasurable
  have hc : Continuous (fun p : (Field n →L[ℝ] Field n) × Field n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  apply hb.of_le_mul (hc.comp_aestronglyMeasurable (hH.prodMk hb.aestronglyMeasurable))
  exact .of_forall fun sample =>
    ((vectorMeasureHessianProcess μ β t ht q sample).le_opNorm (b sample)).trans
      (mul_le_mul_of_nonneg_right (norm_vectorMeasureHessianProcess_le μ β t ht q sample)
        (norm_nonneg _))

theorem vectorMeasure_averaged_random_reaction (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β ≠ 0) (ht : t < 1) (q : Paper.Overlap)
    (b : VectorDisorderBrownianSample n → Field n)
    (hb : MemLp b 2 (vectorMeasureDisorderTilt μ β t a)) :
    (Paper.parisiCDF μ q)^2*
        (∫ sample, vectorMeasureCovarianceQuadratic μ β t a ht.le q sample (b sample)
          ∂vectorMeasureDisorderTilt μ β t a)^2 ≤
      (∫ sample, ‖b sample‖^2 ∂vectorMeasureDisorderTilt μ β t a)*
        ∫ sample, ‖vectorMeasureHessianProcess μ β t ht.le q sample (b sample)‖^2
          ∂vectorMeasureDisorderTilt μ β t a := by
  apply averaged_hilbert_reaction hb
    (memLp_vectorMeasureHessian_random_apply μ β t a ht.le q b hb)
    (integrable_vectorMeasureRandomCovariance μ β t a ht.le q b hb)
  · filter_upwards [vectorMeasureCovarianceQuadratic_nonneg μ β t a hβ ht q] with sample hs
    exact hs (b sample)
  · exact Paper.parisiCDF_nonneg μ q
  · filter_upwards [vectorMeasureHessian_covariance_all_directions μ β t a hβ ht q] with sample hs
    exact (hs (b sample)).1

end QuantitativePaper
