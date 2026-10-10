module
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section

/-! Conditional projection covariance and its residual, with all product
integrals justified by genuine L² hypotheses. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (m : MeasurableSpace Ω) (hm : m≤m₀)
include hm

 theorem integral_conditional_projection_mul {X Y Xbar : Ω→ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (_hXbar : MemLp Xbar 2 P)
    (hYm : AEStronglyMeasurable[m] Y P)
    (hc : P[X|m]=ᵐ[P] Xbar) :
    (∫ω,X ω*Y ω ∂P)=∫ω,Xbar ω*Y ω ∂P := by
  have hp:=condExp_mul_of_aestronglyMeasurable_right hYm
    (hX.integrable_mul hY) (hX.integrable (by norm_num))
  calc
    _=∫ω,P[X*Y|m] ω ∂P:=(integral_condExp hm).symm
    _=∫ω,P[X|m] ω*Y ω ∂P:=integral_congr_ae hp
    _=∫ω,Xbar ω*Y ω ∂P:=integral_congr_ae (hc.mul (.refl _ _))

 theorem covariance_conditional_projection_eq {X Y Xbar Ybar : Ω→ℝ}
    (hX : MemLp X 2 P) (_hY : MemLp Y 2 P)
    (hXbar : MemLp Xbar 2 P) (hYbar : MemLp Ybar 2 P)
    (hcX : P[X|m]=ᵐ[P] Xbar) (hcY : P[Y|m]=ᵐ[P] Ybar) :
    covariance X Ybar P=covariance Xbar Ybar P := by
  have hym : AEStronglyMeasurable[m] Ybar P:=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr hcY
  have hprod:=integral_conditional_projection_mul (m₀:=m₀) P m hm hX hYbar hXbar hym hcX
  have hmean : (∫ω,Xbar ω ∂P)=∫ω,X ω ∂P:=
    (integral_congr_ae hcX.symm).trans (integral_condExp hm)
  rw [covariance_eq_sub hX hYbar,covariance_eq_sub hXbar hYbar,hmean]
  exact congrArg (fun x : ℝ=>x-(∫ω,X ω ∂P)*(∫ω,Ybar ω ∂P)) hprod

 theorem covariance_conditional_residual {X Y Xbar Ybar : Ω→ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hXbar : MemLp Xbar 2 P) (hYbar : MemLp Ybar 2 P)
    (hcX : P[X|m]=ᵐ[P] Xbar) (hcY : P[Y|m]=ᵐ[P] Ybar) :
    covariance X Ybar P-covariance X Y P=
      -(∫ω,(X ω-Xbar ω)*(Y ω-Ybar ω) ∂P) := by
  have hxm : AEStronglyMeasurable[m] Xbar P:=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr hcX
  have hym : AEStronglyMeasurable[m] Ybar P:=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr hcY
  have hp1:=integral_conditional_projection_mul (m₀:=m₀) P m hm hX hYbar hXbar hym hcX
  have hp2 : (∫ω,Xbar ω*Y ω ∂P)=∫ω,Xbar ω*Ybar ω ∂P:=by
    have hh:=integral_conditional_projection_mul (m₀:=m₀) P m hm hY hXbar hYbar hxm hcY
    simpa only [mul_comm] using hh
  have hmean : (∫ω,Ybar ω ∂P)=∫ω,Y ω ∂P:=
    (integral_congr_ae hcY.symm).trans (integral_condExp hm)
  have hres : (∫ω,(X ω-Xbar ω)*(Y ω-Ybar ω) ∂P)=
      (∫ω,X ω*Y ω ∂P)-(∫ω,X ω*Ybar ω ∂P):=by
    have hfun : (fun ω=>(X ω-Xbar ω)*(Y ω-Ybar ω))=
      (X*Y-Xbar*Y)-(X*Ybar-Xbar*Ybar):=by
      funext ω
      simp only [Pi.sub_apply,Pi.mul_apply]
      ring
    rw [hfun]
    change (∫ω,(X*Y-Xbar*Y) ω-(X*Ybar-Xbar*Ybar) ω ∂P)=_
    rw [integral_sub
      ((hX.integrable_mul hY).sub (hXbar.integrable_mul hY))
      ((hX.integrable_mul hYbar).sub (hXbar.integrable_mul hYbar))]
    simp only [Pi.sub_apply]
    rw [integral_sub (hX.integrable_mul hY) (hXbar.integrable_mul hY),
      integral_sub (hX.integrable_mul hYbar) (hXbar.integrable_mul hYbar)]
    simp only [Pi.mul_apply]
    rw [hp1,hp2]
    ring
  rw [covariance_eq_sub hX hYbar,covariance_eq_sub hX hY,hmean,hres]
  simp only [Pi.mul_apply]
  ring

end FourPapersCommon
