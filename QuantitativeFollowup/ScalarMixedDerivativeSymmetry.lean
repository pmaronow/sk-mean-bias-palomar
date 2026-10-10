module
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-! A calculus bridge between genuine derivatives on the coordinate axes
and the symmetric second Fréchet derivative of an actual C² function. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace QuantitativeFollowup
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem scalar_mixed_axis_derivative_eq_hessian (F : ℝ×ℝ→ℝ) (D : ℝ→ℝ) (A : ℝ)
    (hF : ContDiffAt ℝ 2 F (0,0)) (hD : HasDerivAt D A 0)
    (haxis : ∀ᶠ u in 𝓝 (0:ℝ),HasDerivAt (fun v=>F (v,u)) (D u) 0) :
    A=fderiv ℝ (fderiv ℝ F) (0,0) (0,1) (1,0) := by
  have hDF := (hF.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  have hvertical : HasDerivAt (fun u : ℝ=>((0,u):ℝ×ℝ)) (0,1) (0:ℝ) :=
    (hasDerivAt_const (0:ℝ) (0:ℝ)).prodMk (hasDerivAt_id (0:ℝ))
  have hd := hDF.hasFDerivAt.comp_hasDerivAt (f:=fun u : ℝ=>((0,u):ℝ×ℝ)) (0:ℝ) hvertical
  have heval := hd.clm_apply (hasDerivAt_const (0:ℝ) ((1,0):ℝ×ℝ))
  have hval : HasDerivAt (fun u=>fderiv ℝ F (0,u) (1,0))
      (fderiv ℝ (fderiv ℝ F) (0,0) (0,1) (1,0)) 0 := by
    simpa only [Function.comp_apply,map_zero,add_zero] using heval
  have hnear := ((continuous_const.prodMk continuous_id).tendsto (0:ℝ)).eventually
    (hF.eventually (by norm_num : (2:ℕ∞ω)≠∞))
  have he : (fun u=>fderiv ℝ F (0,u) (1,0))=ᶠ[𝓝 (0:ℝ)] D := by
    filter_upwards [hnear,haxis] with u hu haxisu
    have hc : HasDerivAt (fun v : ℝ=>((v,u):ℝ×ℝ)) (1,0) (0:ℝ) :=
      (hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) u)
    have hdu := (hu.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      (f:=fun v : ℝ=>((v,u):ℝ×ℝ)) (0:ℝ) hc
    exact hdu.unique haxisu
  exact hD.unique (hval.congr_of_eventuallyEq he.symm)

theorem scalar_mixed_axis_derivative_symmetric (F : ℝ×ℝ→ℝ) (D E : ℝ→ℝ) (A B : ℝ)
    (hF : ContDiffAt ℝ 2 F (0,0)) (hD : HasDerivAt D A 0) (hE : HasDerivAt E B 0)
    (haxisD : ∀ᶠ u in 𝓝 (0:ℝ),HasDerivAt (fun v=>F (v,u)) (D u) 0)
    (haxisE : ∀ᶠ u in 𝓝 (0:ℝ),HasDerivAt (fun v=>F (u,v)) (E u) 0) : A=B := by
  have h1 := scalar_mixed_axis_derivative_eq_hessian F D A hF hD haxisD
  have hsym := hF.isSymmSndFDerivAt (by norm_num)
  have hDF := (hF.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  have hhorizontal : HasDerivAt (fun u : ℝ=>((u,0):ℝ×ℝ)) (1,0) (0:ℝ) :=
    (hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) (0:ℝ))
  have hd := hDF.hasFDerivAt.comp_hasDerivAt (f:=fun u : ℝ=>((u,0):ℝ×ℝ)) (0:ℝ) hhorizontal
  have heval := hd.clm_apply (hasDerivAt_const (0:ℝ) ((0,1):ℝ×ℝ))
  have hval : HasDerivAt (fun u=>fderiv ℝ F (u,0) (0,1))
      (fderiv ℝ (fderiv ℝ F) (0,0) (1,0) (0,1)) 0 := by
    simpa only [Function.comp_apply,map_zero,add_zero] using heval
  have hnear := ((continuous_id.prodMk continuous_const).tendsto (0:ℝ)).eventually
    (hF.eventually (by norm_num : (2:ℕ∞ω)≠∞))
  have he : (fun u=>fderiv ℝ F (u,0) (0,1))=ᶠ[𝓝 (0:ℝ)] E := by
    filter_upwards [hnear,haxisE] with u hu haxisu
    have hc : HasDerivAt (fun v : ℝ=>((u,v):ℝ×ℝ)) (0,1) (0:ℝ) :=
      (hasDerivAt_const (0:ℝ) u).prodMk (hasDerivAt_id (0:ℝ))
    have hdu := (hu.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      (f:=fun v : ℝ=>((u,v):ℝ×ℝ)) (0:ℝ) hc
    exact hdu.unique haxisu
  have h2 := hE.unique (hval.congr_of_eventuallyEq he.symm)
  rw [h1,h2]
  exact hsym (0,1) (1,0)

end QuantitativeFollowup
