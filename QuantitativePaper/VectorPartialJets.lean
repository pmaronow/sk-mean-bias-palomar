module
public import QuantitativePaper.VectorFiniteCells
public import FourPapersCommon.VectorDriftTaylor

@[expose] public section

/-! Genuine parameter continuity of spatial derivatives obtained from a
joint Frechet-smooth function. The partial derivatives are literal fderiv. -/
noncomputable section
open scoped ContDiff
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_fieldSlice_eq (f : A×E→F) (hf : Differentiable ℝ f) (a : A) (x : E) :
    fderiv ℝ (fun y => f (a,y)) x=
      (fderiv ℝ f (a,x)).comp (ContinuousLinearMap.inr ℝ A E) := by
  have hi : HasFDerivAt (fun y : E => (a,y)) (ContinuousLinearMap.inr ℝ A E) x := by
    convert! (hasFDerivAt_const a x).prodMk (hasFDerivAt_id x) using 1 <;> ext y <;> simp
  exact ((hf (a,x)).hasFDerivAt.comp x hi).fderiv

theorem contDiff_fieldSlice_fderiv (f : A×E→F) {j : ℕ∞ω}
    (hf : ContDiff ℝ (j+1) f) :
    ContDiff ℝ j (fun z : A×E => fderiv ℝ (fun y => f (z.1,y)) z.2) := by
  have he : (fun z : A×E => fderiv ℝ (fun y => f (z.1,y)) z.2)=
      fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ A E) :=
    funext (fun z => fderiv_fieldSlice_eq f (hf.differentiable (by simp)) z.1 z.2)
  rw [he]
  exact (hf.fderiv_right le_rfl).clm_comp contDiff_const

theorem continuous_fieldSlice_hessian (f : A×E→ℝ) (hf : ContDiff ℝ 2 f) :
    Continuous (fun z : A×E => vectorHessian (fun y => f (z.1,y)) z.2) := by
  let g := fun z : A×E => fderiv ℝ (fun y => f (z.1,y)) z.2
  have hg : ContDiff ℝ 1 g := contDiff_fieldSlice_fderiv f (hf.of_le (by norm_num))
  have he : (fun z : A×E => vectorHessian (fun y => f (z.1,y)) z.2)=
      fun z => (fderiv ℝ g z).comp (ContinuousLinearMap.inr ℝ A E) := by
    funext z
    exact fderiv_fieldSlice_eq g (hg.differentiable (by norm_num)) z.1 z.2
  rw [he]
  exact (hg.fderiv_right (m := 0) (by norm_num)).continuous.clm_comp continuous_const

end QuantitativePaper
