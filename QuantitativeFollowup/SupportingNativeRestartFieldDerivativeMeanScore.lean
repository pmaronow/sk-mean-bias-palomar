module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeNativeScore

@[expose] public section

/-! The literal initial-field derivative of the true restarted future
self-overlap. The zero-dimensional case is included by real division. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128

def cavityRestartMeanSquareFieldResponse (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (r : Paper.Overlap) (sample : VectorDisorderBrownianSample n) : ℝ :=
  (∑i : Fin n,cavityRestartSquareFieldResponse D μ g q x w r sample i)/(n:ℝ)

theorem integrable_cavityRestartMeanSquareFieldResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (x w : Field n) :
    Integrable (cavityRestartMeanSquareFieldResponse D μ g q x w r)
      (vectorDisorderBrownianMeasure n) :=
  (integrable_finsetSum _ fun i _=>integrable_cavityRestartSquareFieldResponse D μ g q r hqr x w i).div_const _

theorem fderiv_anisotropicRestartMeanSquare_field_score (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (x w : Field n) :
    fderiv ℝ (fun y=>anisotropicRestartMeanSquare D μ g q y r) x w=
      ∫sample,cavityRestartMeanSquareFieldResponse D μ g q x w r sample
        ∂vectorDisorderBrownianMeasure n := by
  classical
  let F:=fun i : Fin n=>fun y : Field n=>anisotropicRestartSpinSquare D μ g q y i r
  have hd i : DifferentiableAt ℝ (F i) x:=
    (contDiff_anisotropicRestartSpinSquare_field D μ g q r hqr i).differentiable_one x
  have hs:=HasFDerivAt.fun_sum (u:=Finset.univ) (fun i _=>(hd i).hasFDerivAt)
  have hsum : fderiv ℝ (fun y=>anisotropicRestartMeanSquare D μ g q y r) x=
      ((n:ℝ)⁻¹) •∑i : Fin n,fderiv ℝ (F i) x := by
    have hh:=(hs.const_mul ((n:ℝ)⁻¹)).fderiv
    simpa only [F,anisotropicRestartMeanSquare,div_eq_mul_inv,mul_comm] using hh
  rw [hsum]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousLinearMap.sum_apply]
  simp_rw [F,fderiv_anisotropicRestartSpinSquare_field_score D μ g q r hqr]
  rw [←integral_finsetSum Finset.univ (fun i _=>integrable_cavityRestartSquareFieldResponse D μ g q r hqr x w i),
    ←integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    simp only [cavityRestartMeanSquareFieldResponse,div_eq_mul_inv,mul_comm]

end QuantitativeFollowup
