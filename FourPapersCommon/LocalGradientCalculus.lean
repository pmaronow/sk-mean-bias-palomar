module
public import QuantitativeFollowup.CanonicalPosteriorBL

@[expose] public section

/-! Local second-derivative calculus for the genuine Riesz gradient. -/
noncomputable section
open scoped ContDiff
namespace FourPapersCommon

theorem hasFDerivAt_gradient_of_contDiffAt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E→ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (gradient f) (QuantitativeFollowup.hessianOperator f x) x:=by
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).comp
    x ((hf.fderiv_right (by norm_num : (1 : ℕ∞ω)+1 ≤ 2)).differentiableAt (by norm_num)).hasFDerivAt

theorem ringInverse_continuousLinearEquiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : E≃L[ℝ]E) :
    Ring.inverse (e : E→L[ℝ]E)=(e.symm : E→L[ℝ]E):=
  Ring.inverse_unit e.toUnit

end FourPapersCommon
