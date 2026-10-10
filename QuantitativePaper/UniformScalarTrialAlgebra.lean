module
public import QuantitativeFollowup.ScalarClippingCostIdentity
public import QuantitativePaper.UniformScalarSmoothing

@[expose] public section

/-! Energy-coordinate clipping inequalities retain the genuine small-time
contact moment, with coefficients independent of inverse temperature. -/
noncomputable section
open Set MeasureTheory Paper FRSB QuantitativeFollowup
namespace QuantitativePaper
set_option maxHeartbeats 1700000

theorem scalar_energy_clipping_square_algebra (delta gamma M y H z lam C L T : ℝ)
    (hd : 0≤delta) (hdlam : delta≤lam) (hlam : lam≤L)
    (hgam0 : 0≤gamma) (hgamL : gamma≤L) (hM : |M|≤1) (hy : |y|≤2)
    (hH0 : 0≤H) (hHC : H≤C) (hT : 0<T) :
    -(z^2-2*delta*M*H*y-2*gamma*H*y^2-2*(delta*M+gamma*y)*y*z)≤
      (9*L^2+2*L*C+1/T)*y^2+lam^2*C^2*T*M^2 := by
  have hlam0 : 0≤lam := hd.trans hdlam
  have hL0 : 0≤L := hlam0.trans hlam
  have hC0 : 0≤C := hH0.trans hHC
  let A:=delta*M+gamma*y
  have hA : |A|≤3*L := by
    calc
      _≤|delta*M|+|gamma*y|:=abs_add_le _ _
      _=delta*|M|+gamma*|y| := by rw [abs_mul,abs_mul,abs_of_nonneg hd,abs_of_nonneg hgam0]
      _≤L*1+L*2 := add_le_add (mul_le_mul (hdlam.trans hlam) hM (abs_nonneg _) hL0)
        (mul_le_mul hgamL hy (abs_nonneg _) hL0)
      _=_:=by ring
  have hAsq : A^2≤9*L^2 := by nlinarith [sq_abs A,abs_nonneg A]
  have hz : -z^2+2*A*y*z≤9*L^2*y^2 :=
    (show -z^2+2*A*y*z≤A^2*y^2 by nlinarith [sq_nonneg (z-A*y)]).trans
      (mul_le_mul_of_nonneg_right hAsq (sq_nonneg y))
  have hreact : 2*gamma*H*y^2≤2*L*C*y^2 := by
    have hh:=mul_le_mul hgamL hHC hH0 hL0
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg y)]
  have hcross : 2*delta*M*H*y≤y^2/T+lam^2*C^2*T*M^2 := by
    have hprod : M*H*y≤C*|M| *|y| := by
      calc
        _≤|M*H*y|:=le_abs_self _
        _=|M| *H*|y|:=by rw [abs_mul,abs_mul,abs_of_nonneg hH0]
        _≤|M| *C*|y|:=by gcongr
        _=_:=by ring
    have hdelta:=mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num : (0:ℝ)≤2) hd)
    have hlim : 2*delta*C*|M| *|y|≤2*(lam*C)*|M| *|y| := by
      convert mul_le_mul_of_nonneg_right hdlam
        (show 0≤2*C*|M| *|y| by positivity) using 1 <;> ring
    have hYoung:=clipping_young (lam*C) T M y hT
    calc
      _≤2*delta*C*|M| *|y| := by convert hdelta using 1 <;> ring
      _≤2*(lam*C)*|M| *|y| := hlim
      _≤_ := by convert hYoung using 1 <;> ring
  dsimp only [A] at hz
  simp only [div_eq_mul_inv] at hcross ⊢
  nlinarith only [hz,hreact,hcross]

theorem scalar_energy_clipping_cost_algebra (delta gamma M y lam L T : ℝ)
    (hd : 0≤delta) (hdlam : delta≤lam) (hgamL : gamma≤L) (hT : 0<T) :
    (1/2:ℝ)*(2*delta*M*y+gamma*y^2)≤
      (1/2:ℝ)*((1/T+L)*y^2+lam^2*T*M^2) := by
  have hh : M*y≤|M| *|y| := by simpa only [abs_mul] using le_abs_self (M*y)
  have h1:=mul_le_mul_of_nonneg_left hh (mul_nonneg (by norm_num : (0:ℝ)≤2) hd)
  have h2 : 2*delta*|M| *|y|≤2*lam*|M| *|y| := by gcongr
  have h3:=clipping_young lam T M y hT
  have h4:=mul_le_mul_of_nonneg_right hgamL (sq_nonneg y)
  simp only [div_eq_mul_inv] at h3 ⊢
  nlinarith only [h1,h2,h3,h4]

theorem scalarClippingSquareSource_uniform_energy_le (β : ℝ) (hβ : 0<β)
    (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) (ht : p.1∈Icc (0:ℝ) 1)
    (lam C L T : ℝ) (hT : 0<T)
    (hv : parisiCDF μ p.1≤parisiCDF ν p.1)
    (hdelta : β*(parisiCDF ν p.1-parisiCDF μ p.1)≤lam) (hlam : lam≤L)
    (hgam : β*parisiCDF ν p.1≤L) (hH : β*parisiHessian β μ p≤C) :
    -scalarClippingSquareSource β μ ν p≤
      (9*L^2+2*L*C+1/T)*scalarGradientDifference β μ ν p^2+
        lam^2*C^2*T*parisiGradient β μ p^2 := by
  have hh:=scalar_energy_clipping_square_algebra
    (β*(parisiCDF ν p.1-parisiCDF μ p.1)) (β*parisiCDF ν p.1)
    (parisiGradient β μ p) (scalarGradientDifference β μ ν p)
    (β*parisiHessian β μ p) (β*scalarCurvatureDifference β μ ν p) lam C L T
    (mul_nonneg hβ.le (sub_nonneg.mpr hv)) hdelta hlam
    (mul_nonneg hβ.le (parisiCDF_nonneg ν p.1)) hgam
    (by simpa only [←Real.norm_eq_abs] using norm_parisiGradient_le_one β μ p)
    (by simpa only [←Real.norm_eq_abs] using norm_scalarGradientDifference_le β μ ν p)
    (mul_nonneg hβ.le (parisiHessian_pos_all β μ p.1 p.2 ht).le) hH hT
  unfold scalarClippingSquareSource
  convert hh using 1 <;> ring

theorem scalarClippingCostSource_uniform_energy_le (β : ℝ) (hβ : 0<β)
    (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) (lam L T : ℝ) (hT : 0<T)
    (hv : parisiCDF μ p.1≤parisiCDF ν p.1)
    (hdelta : β*(parisiCDF ν p.1-parisiCDF μ p.1)≤lam)
    (hgam : β*parisiCDF ν p.1≤L) :
    scalarClippingCostSource β μ ν p/β≤
      (1/2:ℝ)*((1/T+L)*scalarGradientDifference β μ ν p^2+
        lam^2*T*parisiGradient β μ p^2) := by
  have hh:=scalar_energy_clipping_cost_algebra
    (β*(parisiCDF ν p.1-parisiCDF μ p.1)) (β*parisiCDF ν p.1)
    (parisiGradient β μ p) (scalarGradientDifference β μ ν p) lam L T
    (mul_nonneg hβ.le (sub_nonneg.mpr hv)) hdelta hgam hT
  unfold scalarClippingCostSource
  convert hh using 1 <;> field_simp <;> ring

end QuantitativePaper
