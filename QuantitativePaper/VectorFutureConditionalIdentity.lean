module
public import QuantitativePaper.VectorFutureMeanSquareKernelIntegral

@[expose] public section

/-! Actual conditional Hessian identity for every arbitrary profile,
including atoms, under the complete enlarged Wiener/disorder past. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorMeasureHessian_future_conditional_mean (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β ≠ 0) (ht : t < 1) (q : Paper.Overlap) (w : Field n) :
    (vectorMeasureDisorderTilt μ β t a)[vectorMeasureTerminalSecondMoment μ β t ht.le w |
      vectorBrownianFiltration n (q:ℝ).toNNReal] =ᵐ[vectorMeasureDisorderTilt μ β t a]
      fun p => vectorMeasureHessianQuadratic μ β t ht.le q w p +
        Paper.parisiCDF μ q*(vectorMeasureMeanInDirection μ β t ht.le q w p)^2 +
        vectorFutureMeanSquareKernelIntegral μ β t a q ht.le w p := by
  let ambient : MeasurableSpace (VectorDisorderBrownianSample n) := inferInstance
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  letI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  let V := vectorBrownianFiltration n (q:ℝ).toNNReal
  letI : MeasurableSpace (VectorDisorderBrownianSample n) := ambient
  let H := vectorMeasureHessianQuadratic μ β t ht.le q w
  let M := fun p => Paper.parisiCDF μ q*(vectorMeasureMeanInDirection μ β t ht.le q w p)^2
  let F := vectorFutureMeanSquareKernelIntegral μ β t a q ht.le w
  have hHi : Integrable H P := integrable_vectorMeasureHessianQuadratic μ β t a ht.le q w
  have hMi : Integrable M P := (integrable_vectorMeasureMeanInDirection_sq μ β t a ht.le q w).const_mul _
  have hFi : Integrable F P := integrable_vectorFutureMeanSquareKernelIntegral μ β t a q ht.le w
  have hGi : Integrable (fun p => H p+M p+F p) P := (hHi.add hMi).add hFi
  have hGm : StronglyMeasurable[V] (fun p => H p+M p+F p) :=
    (((adapted_vectorMeasureHessianQuadratic μ β t ht.le q w).stronglyMeasurable.add
      (((adapted_vectorMeasureMeanInDirection μ β t ht.le q w).pow_const 2).stronglyMeasurable.const_mul _)).add
      (adapted_vectorFutureMeanSquareKernelIntegral μ β t a q ht.le w))
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq ((vectorBrownianFiltration n).le _)
    (integrable_vectorMeasureTerminalSecondMoment μ β t a ht.le w)
  · intro A _ _
    exact hGi.integrableOn
  · intro A hA _
    let Z : VectorDisorderBrownianSample n → ℝ := A.indicator (fun _ => 1)
    have hZ : Measurable[V] Z := measurable_const.indicator hA
    have hZb : ∀p, ‖Z p‖ ≤ (1:ℝ≥0) := fun p => by
      by_cases hp : p ∈ A <;> simp [Z, hp]
    have he := vectorMeasure_future_mean_loss μ β t a hβ ht q w Z hZ 1 hZb
    rw [←vectorFutureMeanSquareKernelIntegral_weighted_pairing μ β t a q ht.le w Z hZ 1 hZb] at he
    have hAg : MeasurableSet A := ((vectorBrownianFiltration n).le _) A hA
    change (∫p, Z p*H p ∂P) + Paper.parisiCDF μ q*(∫p,
        Z p*(vectorMeasureMeanInDirection μ β t ht.le q w p)^2 ∂P) +
        (∫p, Z p*F p ∂P) = ∫p, Z p*vectorMeasureTerminalSecondMoment μ β t ht.le w p ∂P at he
    dsimp only [Z] at he
    rw [integral_indicator_one_mul_eq_setIntegral P A hAg H,
      integral_indicator_one_mul_eq_setIntegral P A hAg,
      integral_indicator_one_mul_eq_setIntegral P A hAg F,
      integral_indicator_one_mul_eq_setIntegral P A hAg] at he
    change (∫p in A, (H+M) p+F p ∂P) =
      ∫p in A, vectorMeasureTerminalSecondMoment μ β t ht.le w p ∂P
    rw [integral_add (hHi.add hMi).integrableOn hFi.integrableOn]
    simp only [Pi.add_apply]
    rw [integral_add hHi.integrableOn hMi.integrableOn]
    change _ + (∫p in A, Paper.parisiCDF μ q*
      (vectorMeasureMeanInDirection μ β t ht.le q w p)^2 ∂P) + _ = _
    rw [integral_const_mul]
    exact he
  · exact hGm.aestronglyMeasurable

end QuantitativePaper
