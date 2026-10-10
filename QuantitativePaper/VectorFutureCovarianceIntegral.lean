module
public import QuantitativePaper.VectorFutureConditionalIdentity

@[expose] public section

/-! The literal arbitrary-profile conditional covariance integral.
The integrand is a jointly measurable version of E_q C_u, obtained from
the true conditional law of the whole continuous mean path and the tower law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorMeasureExpectedFutureCovariance (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (q : Paper.Overlap) (ht : t ≤ 1) (u : Paper.Overlap) (w : Field n)
    (p : VectorDisorderBrownianSample n) : ℝ :=
  ((vectorMeasureDisorderTilt μ β t a)[vectorMeasureTerminalSecondMoment μ β t ht w |
    vectorBrownianFiltration n (q:ℝ).toNNReal]) p - vectorPastMeanSquareKernel μ β t a q ht u w p

theorem vectorMeasureExpectedFutureCovariance_condExp (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (q u : Paper.Overlap) (ht : t ≤ 1) (hqu : q ≤ u) (w : Field n) :
    (vectorMeasureDisorderTilt μ β t a)[vectorMeasureConditionalVariance μ β t a ht u w |
      vectorBrownianFiltration n (q:ℝ).toNNReal] =ᵐ[vectorMeasureDisorderTilt μ β t a]
      vectorMeasureExpectedFutureCovariance μ β t a q ht u w := by
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  letI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have hs := condExp_sub (μ:=P)
    (integrable_condExp (μ:=P) (f:=vectorMeasureTerminalSecondMoment μ β t ht w)
      (m:=vectorBrownianFiltration n (u:ℝ).toNNReal))
    (integrable_vectorMeasureMeanInDirection_sq μ β t a ht u w)
    (vectorBrownianFiltration n (q:ℝ).toNNReal)
  have htw := condExp_condExp_of_le (μ:=P) (f:=vectorMeasureTerminalSecondMoment μ β t ht w)
    ((vectorBrownianFiltration n).mono (Real.toNNReal_mono hqu)) ((vectorBrownianFiltration n).le _)
  have hsq := vectorPastMeanSquareKernel_condExp μ β t a q ht u w
  change P[(P[vectorMeasureTerminalSecondMoment μ β t ht w |
    vectorBrownianFiltration n (u:ℝ).toNNReal] -
    (fun p => (vectorMeasureMeanInDirection μ β t ht u w p)^2)) |
    vectorBrownianFiltration n (q:ℝ).toNNReal] =ᵐ[P] _
  filter_upwards [hs, htw, hsq] with p hp htp hsp
  change _ = ((P[vectorMeasureTerminalSecondMoment μ β t ht w |
    vectorBrownianFiltration n (q:ℝ).toNNReal]) p - vectorPastMeanSquareKernel μ β t a q ht u w p)
  simp only [Pi.sub_apply] at hp
  rw [htp] at hp
  change (P[(fun p => (vectorMeasureMeanInDirection μ β t ht u w p)^2) |
    vectorBrownianFiltration n (q:ℝ).toNNReal]) p = vectorPastMeanSquareKernel μ β t a q ht u w p at hsp
  rw [hsp] at hp
  exact hp

theorem vectorMeasureExpectedFutureCovariance_integral (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (q : Paper.Overlap) (ht : t ≤ 1) (w : Field n)
    (p : VectorDisorderBrownianSample n) :
    (∫u : Paper.Overlap, if q < u then vectorMeasureExpectedFutureCovariance μ β t a q ht u w p else 0
      ∂(μ:Measure Paper.Overlap)) =
      (1-Paper.parisiCDF μ q)*((vectorMeasureDisorderTilt μ β t a)[
        vectorMeasureTerminalSecondMoment μ β t ht w | vectorBrownianFiltration n (q:ℝ).toNNReal]) p -
      vectorFutureMeanSquareKernelIntegral μ β t a q ht w p := by
  let T := ((vectorMeasureDisorderTilt μ β t a)[vectorMeasureTerminalSecondMoment μ β t ht w |
    vectorBrownianFiltration n (q:ℝ).toNNReal]) p
  let K := fun u : Paper.Overlap => if q < u then vectorPastMeanSquareKernel μ β t a q ht u w p else 0
  have hmeas : Measurable (fun u : Paper.Overlap => vectorPastMeanSquareKernel μ β t a q ht u w p) :=
    (measurable_uncurry_vectorPastMeanSquareKernel μ β t a q ht w).comp
      (measurable_id.prodMk measurable_const)
  have hki : Integrable K (μ:Measure Paper.Overlap) := by
    apply (integrable_const ((vectorDirectionBound w)^2)).mono'
      (Measurable.ite (measurableSet_lt measurable_const measurable_id) hmeas measurable_const).aestronglyMeasurable
    exact .of_forall fun u => by
      split_ifs
      · exact norm_vectorPastMeanSquareKernel_le μ β t a q ht u w p
      · simp only [norm_zero]
        exact sq_nonneg _
  have hS : MeasurableSet {u : Paper.Overlap | q < u} := measurableSet_lt measurable_const measurable_id
  have hci : Integrable ({u : Paper.Overlap | q < u}.indicator (fun _ => T)) (μ:Measure Paper.Overlap) :=
    (integrable_const T).indicator hS
  have he : (fun u : Paper.Overlap => if q < u then vectorMeasureExpectedFutureCovariance μ β t a q ht u w p else 0) =
      fun u => {u : Paper.Overlap | q < u}.indicator (fun _ => T) u-K u := by
    funext u
    by_cases hqu : q < u <;> simp [vectorMeasureExpectedFutureCovariance, T, K, hqu]
  rw [he, integral_sub hci hki, integral_indicator_const T hS, smul_eq_mul, parisi_future_mass]
  rfl

theorem vectorMeasureHessian_future_covariance_integral (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β ≠ 0) (ht : t < 1) (q : Paper.Overlap) (w : Field n) :
    ∀ᵐp ∂vectorMeasureDisorderTilt μ β t a,
      vectorMeasureHessianQuadratic μ β t ht.le q w p =
        Paper.parisiCDF μ q*vectorMeasureConditionalVariance μ β t a ht.le q w p +
        ∫u : Paper.Overlap, if q < u then vectorMeasureExpectedFutureCovariance μ β t a q ht.le u w p else 0
          ∂(μ:Measure Paper.Overlap) := by
  filter_upwards [vectorMeasureHessian_future_conditional_mean μ β t a hβ ht q w] with p hp
  rw [vectorMeasureExpectedFutureCovariance_integral]
  unfold vectorMeasureConditionalVariance
  simp only [Pi.sub_apply]
  linarith

end QuantitativePaper
