module
public import FourPapersCommon.GaussianTiltedCurvature

@[expose] public section

/-! The genuine Gaussian localization theorem in uncentered density form,
with all exponential and observable integrability proved. This form can be
averaged over independent conditioned coordinates by Fubini. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology
namespace FourPapersCommon
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => SYK.standardGaussianMeasureOnEuclidean ι

theorem gaussian_tilted_curvature_raw (V m H : E→ℝ)
    (hV : ContDiff ℝ 1 V) (hm : ContDiff ℝ 1 m) (hH : Continuous H)
    (K B : ℝ) (hK : 0<K) (hHbound : ∀x,|H x|≤B)
    (hDV : ∀x,‖fderiv ℝ V x‖≤K) (hDm : ∀x,‖fderiv ℝ m x‖≤H x)
    (hmb : ∀x,|m x|≤1) (hdiag : ∀x,1-|m x|≤H x)
    (heven : ∀x,V (-x)=V x) (hodd : ∀x,m (-x)= -m x) :
    Integrable (fun x=>Real.exp (V x)) P ∧
    Integrable (fun x=>Real.exp (V x)*H x) P ∧
    Real.exp (-8*Real.sqrt (Real.pi/2)*K-K^2/2)/(2*(1+Real.sqrt (Real.pi/2)))*
      (∫x,Real.exp (V x)∂P) ≤ ∫x,Real.exp (V x)*H x∂P := by
  let A := ∫y,V y∂P
  let W := fun x:E=>Real.exp (V x-A)
  have hLip : LipschitzWith K.toNNReal V := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hV.differentiable (by norm_num))
    intro x
    rw [←NNReal.coe_le_coe,coe_nnnorm,Real.coe_toNNReal K hK.le]
    exact hDV x
  have hWi : Integrable W P := by
    simpa only [one_mul] using
      (SYK.product_standardGaussian_hasSubgaussianMGF V K hK hLip).integrable_exp_mul 1
  have hraw : (fun x=>Real.exp (V x)) = fun x=>Real.exp A*W x := by
    funext x
    rw [←Real.exp_add]
    congr 1
    ring
  have hI : Integrable (fun x=>Real.exp (V x)) P := by
    rw [hraw]
    exact hWi.const_mul _
  have hIH : Integrable (fun x=>Real.exp (V x)*H x) P :=
    hI.mul_bdd hH.aestronglyMeasurable (.of_forall fun x=>by
      simpa only [Real.norm_eq_abs] using hHbound x)
  have hZH : 0<∫x,W x∂P := integral_exp_pos hWi
  have hlow := (le_div_iff₀ hZH).mp
    (gaussian_tilted_curvature_lower V m H hV hm hH K B hK hHbound hDV hDm hmb hdiag heven hodd)
  have hWHi : Integrable (fun x=>W x*H x) P :=
    hWi.mul_bdd hH.aestronglyMeasurable (.of_forall fun x=>by
      simpa only [Real.norm_eq_abs] using hHbound x)
  have hrawH : (fun x=>Real.exp (V x)*H x)=fun x=>Real.exp A*(W x*H x) := by
    funext x
    rw [congrFun hraw x]
    ring
  refine ⟨hI,hIH,?_⟩
  rw [hrawH,hraw,integral_const_mul,integral_const_mul]
  simpa only [mul_assoc,mul_left_comm] using
    mul_le_mul_of_nonneg_left hlow (Real.exp_pos A).le

end FourPapersCommon
