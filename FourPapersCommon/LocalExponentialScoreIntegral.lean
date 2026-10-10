module
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! Actual differentiation of an exponentially weighted integral. Local
derivative bounds and the base exponential moment derive the common
integrable envelope; no derivative of the integral is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 1400000
variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace α]

theorem hasFDerivAt_local_exponential_score_integral
    (μ : Measure α) (L f : E → α → ℝ)
    (DL Df : E → α → E →L[ℝ] ℝ) (x0 : E) (r CL Cf Cd : ℝ)
    (hr : 0<r) (hCL : 0 ≤ CL) (hCf : 0 ≤ Cf) (hCd : 0 ≤ Cd)
    (hLm : ∀x∈Metric.ball x0 r,AEStronglyMeasurable (L x) μ)
    (hfm : ∀x∈Metric.ball x0 r,AEStronglyMeasurable (f x) μ)
    (hDLm : AEStronglyMeasurable (DL x0) μ)
    (hDfm : AEStronglyMeasurable (Df x0) μ)
    (hI : Integrable (fun z=>Real.exp (L x0 z)) μ)
    (hLip : ∀z x,x∈Metric.ball x0 r → L x z-L x0 z ≤ CL*‖x-x0‖)
    (hfBound : ∀z x,x∈Metric.ball x0 r → |f x z| ≤ Cf)
    (hDLBound : ∀z x,x∈Metric.ball x0 r → ‖DL x z‖ ≤ CL)
    (hDfBound : ∀z x,x∈Metric.ball x0 r → ‖Df x z‖ ≤ Cd)
    (hDL : ∀z x,x∈Metric.ball x0 r → HasFDerivAt (fun y=>L y z) (DL x z) x)
    (hDf : ∀z x,x∈Metric.ball x0 r → HasFDerivAt (fun y=>f y z) (Df x z) x) :
    Integrable (fun z=>Real.exp (L x0 z) • (Df x0 z+f x0 z • DL x0 z)) μ ∧
    HasFDerivAt (fun x=>∫z,Real.exp (L x z)*f x z ∂μ)
      (∫z,Real.exp (L x0 z) • (Df x0 z+f x0 z • DL x0 z) ∂μ) x0 := by
  have hx0 : x0∈Metric.ball x0 r:=Metric.mem_ball_self hr
  let D : E → α → E →L[ℝ] ℝ:=fun x z=>Real.exp (L x z) • (Df x z+f x z • DL x z)
  let B : α → ℝ:=fun z=>((Cd+Cf*CL)*Real.exp (CL*r))*Real.exp (L x0 z)
  have hEm (x : E) (hx : x∈Metric.ball x0 r) :
      AEStronglyMeasurable (fun z=>Real.exp (L x z)) μ:=
    Real.continuous_exp.comp_aestronglyMeasurable (hLm x hx)
  have hDm : AEStronglyMeasurable (D x0) μ:=(hEm x0 hx0).smul
    (hDfm.add ((hfm x0 hx0).smul hDLm))
  have hBi : Integrable B μ:=hI.const_mul _
  have hExp (z : α) (x : E) (hx : x∈Metric.ball x0 r) :
      Real.exp (L x z) ≤ Real.exp (CL*r)*Real.exp (L x0 z) := by
    have hxnorm : ‖x-x0‖ < r:=by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh:=mul_le_mul_of_nonneg_left hxnorm.le hCL
    linarith [hLip z x hx]
  have hDb (z : α) (x : E) (hx : x∈Metric.ball x0 r) : ‖D x z‖ ≤ B z := by
    have hd : ‖Df x z+f x z • DL x z‖ ≤ Cd+Cf*CL:=by
      apply (norm_add_le _ _).trans
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add (hDfBound z x hx)
        (mul_le_mul (hfBound z x hx) (hDLBound z x hx) (norm_nonneg _) hCf)
    change ‖Real.exp (L x z) • (Df x z+f x z • DL x z)‖ ≤ B z
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have hh:=mul_le_mul (hExp z x hx) hd (norm_nonneg _) (by positivity)
    convert hh using 1 <;> dsimp only [B] <;> ring
  have hi : Integrable (fun z=>Real.exp (L x0 z)*f x0 z) μ:=by
    apply (hI.const_mul Cf).mono' ((hEm x0 hx0).mul (hfm x0 hx0))
    exact .of_forall fun z=>by
      change ‖Real.exp (L x0 z)*f x0 z‖ ≤ Cf*Real.exp (L x0 z)
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hfBound z x0 hx0)
        (Real.exp_pos _).le
  refine ⟨hBi.mono' hDm (.of_forall fun z=>hDb z x0 hx0),?_⟩
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F:=fun x z=>Real.exp (L x z)*f x z) (F':=D) (bound:=B)
    (Metric.ball_mem_nhds x0 hr)
  · filter_upwards [Metric.ball_mem_nhds x0 hr] with x hx
    exact (hEm x hx).mul (hfm x hx)
  · exact hi
  · exact hDm
  · exact .of_forall fun z x hx=>hDb z x hx
  · exact hBi
  · exact .of_forall fun z x hx=>by
      have hh:=((hDL z x hx).exp).mul (hDf z x hx)
      convert hh using 1
      ext v
      simp only [D,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
      ring

end FourPapersCommon
