module
public import QuantitativeFollowup.ScalarClippingGenerator
public import FourPapersCommon.IntegralGronwall

@[expose] public section

/-! Weighted Young estimates preserve the third power of the localization
length. They avoid replacing the true small-time magnetization moment by a
constant, which would lose the fifth-order trial cost. -/
noncomputable section
open Set MeasureTheory Paper FRSB FourPapersCommon
namespace QuantitativeFollowup

theorem clipping_young (s T M y : ℝ) (hT : 0<T) :
    2*s*|M| * |y|≤y^2/T+s^2*T*M^2 := by
  apply le_of_mul_le_mul_left (a:=T) _ hT
  have hh:=sq_nonneg (T*s*|M| - |y|)
  rw [sub_sq,mul_pow,mul_pow,sq_abs,sq_abs] at hh
  rw [mul_add,mul_div_cancel₀ _ hT.ne']
  nlinarith only [hh]

theorem scalarClippingSquareSource_weighted_energy_le (β s T : ℝ)
    (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) (ht : p.1∈Icc (0:ℝ) 1)
    (hT : 0<T) (hv : parisiCDF μ p.1≤parisiCDF ν p.1)
    (hvs : parisiCDF ν p.1-parisiCDF μ p.1≤ s) :
    -scalarClippingSquareSource β μ ν p≤β^2*(
      (11+1/T)*scalarGradientDifference β μ ν p^2+s^2*T*parisiGradient β μ p^2) := by
  have h:=scalarClippingSquareSource_energy_le β μ ν p ht hv
  have hy:=clipping_young s T (parisiGradient β μ p) (scalarGradientDifference β μ ν p) hT
  have hvy : 2*(parisiCDF ν p.1-parisiCDF μ p.1)*|parisiGradient β μ p| *
      |scalarGradientDifference β μ ν p|≤2*s*|parisiGradient β μ p| * |scalarGradientDifference β μ ν p| := by
    gcongr
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  convert! add_le_add_left (hvy.trans hy) (11*scalarGradientDifference β μ ν p^2) using 1 <;> ring

theorem le_exp_of_reverse_integral_le (f : ℝ→ℝ) (hf : Continuous f) (T δ K : ℝ)
    (hδ : 0≤δ) (hK : 0≤K)
    (hf0 : ∀r∈Icc (0:ℝ) T,0≤f r)
    (hineq : ∀r∈Icc (0:ℝ) T,f r≤δ+K*(∫s in r..T,f s)) :
    ∀r∈Icc (0:ℝ) T,f r≤δ*Real.exp (K*(T-r)) := by
  have hrev : Continuous (fun r=>f (T-r)):=hf.comp (continuous_const.sub continuous_id)
  have hh:=le_exp_of_integral_le (fun r=>f (T-r)) hrev T δ K hδ hK
    (fun r hr=>hf0 (T-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩)
    (by
      intro r hr
      simpa only [intervalIntegral.integral_comp_sub_left,sub_zero] using
        hineq (T-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩)
  intro r hr
  have hrr : T-r∈Icc (0:ℝ) T:=⟨by linarith [hr.2],by linarith [hr.1]⟩
  simpa only [sub_sub_cancel] using hh (T-r) hrr

end QuantitativeFollowup
