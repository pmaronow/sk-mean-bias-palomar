module
public import QuantitativeFollowup.ScalarSquareEnergy

@[expose] public section

/-! Literal residual clipping cost and its weighted Young bound. The
linear term is exactly the minimizing diffusion's contact moment. -/
noncomputable section
open Set MeasureTheory Paper FRSB
namespace QuantitativeFollowup
set_option maxHeartbeats 600000

def scalarClippingCostSource (β : ℝ) (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) : ℝ:=
  β^2/2*(2*(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p*
    scalarGradientDifference β μ ν p+parisiCDF ν p.1*scalarGradientDifference β μ ν p^2)

theorem scalarClippingCostSource_eq (β : ℝ) (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) :
    -scalarClippingPotentialSource β μ ν p=β^2/2*(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p^2+
      scalarClippingCostSource β μ ν p := by
  unfold scalarClippingPotentialSource scalarClippingCostSource
  ring

@[fun_prop] theorem measurable_scalarClippingCostSource (β : ℝ) (μ ν : Paper.ParisiMeasure) :
    Measurable (scalarClippingCostSource β μ ν) := by
  have hμ : Measurable (fun p : ℝ×ℝ=>parisiCDF μ p.1):=(parisiCDF_measurable μ).comp measurable_fst
  have hν : Measurable (fun p : ℝ×ℝ=>parisiCDF ν p.1):=(parisiCDF_measurable ν).comp measurable_fst
  have hM:=(continuous_parisiGradient β μ).measurable
  have hy:=(continuous_scalarGradientDifference β μ ν).measurable
  exact measurable_const.mul ((((measurable_const.mul (hν.sub hμ)).mul hM).mul hy |>.add
    (hν.mul (hy.pow_const 2))))

theorem norm_scalarClippingCostSource_le (β : ℝ) (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) :
    ‖scalarClippingCostSource β μ ν p‖≤4*β^2 := by
  have he : scalarClippingCostSource β μ ν p=
      -scalarClippingPotentialSource β μ ν p-β^2/2*(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p^2 := by
    linarith [scalarClippingCostSource_eq β μ ν p]
  have hα : ‖parisiCDF ν p.1‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (parisiCDF_nonneg ν p.1)]
    exact parisiCDF_le_one ν p.1
  have hv:=norm_parisiCDF_sub_le_one ν μ p.1
  have hM:=norm_parisiGradient_le_one β μ p
  have hy:=norm_scalarGradientDifference_le β μ ν p
  have h₁ : ‖2*(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p*scalarGradientDifference β μ ν p‖≤4 := by
    simp only [norm_mul,Real.norm_ofNat]
    calc
      (2:ℝ)*‖parisiCDF ν p.1-parisiCDF μ p.1‖*‖parisiGradient β μ p‖*‖scalarGradientDifference β μ ν p‖≤2*1*1*2 := by gcongr
      _=4 := by norm_num
  have h₂ : ‖parisiCDF ν p.1*scalarGradientDifference β μ ν p^2‖≤4 := by
    rw [norm_mul,norm_pow]
    calc
      ‖parisiCDF ν p.1‖*‖scalarGradientDifference β μ ν p‖^2≤1*2^2 := by gcongr
      _=4 := by norm_num
  unfold scalarClippingCostSource
  rw [norm_mul,Real.norm_of_nonneg (by positivity : (0:ℝ)≤β^2/2)]
  have hh:=(norm_add_le _ _).trans (add_le_add h₁ h₂)
  nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ)≤β^2/2)]

theorem scalarClippingCostSource_weighted_le (β s T : ℝ) (μ ν : Paper.ParisiMeasure)
    (p : ℝ×ℝ) (hT : 0<T) (hv : parisiCDF μ p.1≤parisiCDF ν p.1)
    (hvs : parisiCDF ν p.1-parisiCDF μ p.1 ≤ s) :
    scalarClippingCostSource β μ ν p≤β^2/2*((1/T+1)*scalarGradientDifference β μ ν p^2+
      s^2*T*parisiGradient β μ p^2) := by
  have hv0:0≤parisiCDF ν p.1-parisiCDF μ p.1:=sub_nonneg.mpr hv
  have hm:parisiGradient β μ p*scalarGradientDifference β μ ν p≤
      |parisiGradient β μ p| * |scalarGradientDifference β μ ν p| := by
    simpa only [abs_mul] using le_abs_self (parisiGradient β μ p*scalarGradientDifference β μ ν p)
  have hy:=clipping_young s T (parisiGradient β μ p) (scalarGradientDifference β μ ν p) hT
  have hmul:=mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num : (0:ℝ)≤2) hv0)
  have hvy : 2*(parisiCDF ν p.1-parisiCDF μ p.1)*|parisiGradient β μ p| *
      |scalarGradientDifference β μ ν p|≤2*s*|parisiGradient β μ p| * |scalarGradientDifference β μ ν p| := by gcongr
  have hα:=mul_le_mul_of_nonneg_right (parisiCDF_le_one ν p.1)
    (sq_nonneg (scalarGradientDifference β μ ν p))
  unfold scalarClippingCostSource
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ)≤β^2/2)
  have hh : 2*(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p*scalarGradientDifference β μ ν p≤
      scalarGradientDifference β μ ν p^2/T+s^2*T*parisiGradient β μ p^2 := by
    calc
      _ ≤ 2*(parisiCDF ν p.1-parisiCDF μ p.1)*|parisiGradient β μ p| * |scalarGradientDifference β μ ν p| := by
        convert! hmul using 1 <;> ring
      _ ≤ _ := hvy.trans hy
  convert! add_le_add hh hα using 1 <;> ring

end QuantitativeFollowup
