module
public import QuantitativeFollowup.ScalarClippingGenerator

@[expose] public section

/-! Genuine uniform bounds and measurability of the clipping sources. -/
noncomputable section
open Set MeasureTheory Paper FRSB
namespace QuantitativeFollowup
set_option maxHeartbeats 500000

@[fun_prop] theorem continuous_scalarGradientDifference (β : ℝ) (μ ν : Paper.ParisiMeasure) :
    Continuous (scalarGradientDifference β μ ν) :=
  (continuous_parisiGradient β ν).sub (continuous_parisiGradient β μ)

@[fun_prop] theorem continuous_scalarCurvatureDifference (β : ℝ) (μ ν : Paper.ParisiMeasure) :
    Continuous (scalarCurvatureDifference β μ ν) :=
  (continuous_parisiHessian_all β ν).sub (continuous_parisiHessian_all β μ)

theorem norm_scalarClippingPotentialSource_le (β : ℝ) (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) :
    ‖scalarClippingPotentialSource β μ ν p‖≤5*β^2 := by
  have hα : ‖parisiCDF ν p.1‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (parisiCDF_nonneg ν p.1)]
    exact parisiCDF_le_one ν p.1
  have hv:=norm_parisiCDF_sub_le_one ν μ p.1
  have hM:=norm_parisiGradient_le_one β μ p
  have hy:=norm_scalarGradientDifference_le β μ ν p
  have h₁ : ‖(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p^2‖≤1 := by
    rw [norm_mul,norm_pow]
    calc
      ‖parisiCDF ν p.1-parisiCDF μ p.1‖ * ‖parisiGradient β μ p‖^2 ≤ (1:ℝ)*1^2 := by gcongr
      _=1 := by norm_num
  have h₂ : ‖2*(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p*
      scalarGradientDifference β μ ν p‖≤4 := by
    simp only [norm_mul, Real.norm_ofNat]
    calc
      (2:ℝ) * ‖parisiCDF ν p.1-parisiCDF μ p.1‖ * ‖parisiGradient β μ p‖ * ‖scalarGradientDifference β μ ν p‖ ≤ (2:ℝ)*1*1*2 := by gcongr
      _=4 := by norm_num
  have h₃ : ‖parisiCDF ν p.1*scalarGradientDifference β μ ν p^2‖≤4 := by
    rw [norm_mul,norm_pow]
    calc
      ‖parisiCDF ν p.1‖ * ‖scalarGradientDifference β μ ν p‖^2 ≤ (1:ℝ)*2^2 := by gcongr
      _=4 := by norm_num
  unfold scalarClippingPotentialSource
  rw [norm_mul,norm_neg,Real.norm_of_nonneg (by positivity : (0:ℝ)≤β^2/2)]
  have hb : ‖(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p^2+
      2*(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p*
        scalarGradientDifference β μ ν p+parisiCDF ν p.1*scalarGradientDifference β μ ν p^2‖≤9 := by
    calc
      _ ≤ (‖(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p^2‖ +
        ‖2*(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p*scalarGradientDifference β μ ν p‖)+
        ‖parisiCDF ν p.1*scalarGradientDifference β μ ν p^2‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 9 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ)≤β^2/2)]

theorem norm_scalarClippingSquareSource_le (β : ℝ) (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) :
    ‖scalarClippingSquareSource β μ ν p‖≤40*β^2 := by
  have hα : ‖parisiCDF ν p.1‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (parisiCDF_nonneg ν p.1)]
    exact parisiCDF_le_one ν p.1
  have hv:=norm_parisiCDF_sub_le_one ν μ p.1
  have hM:=norm_parisiGradient_le_one β μ p
  have hC:=norm_parisiHessian_le_one_all β μ p
  have hy:=norm_scalarGradientDifference_le β μ ν p
  have hz:=norm_scalarCurvatureDifference_le β μ ν p
  have h₁ : ‖scalarCurvatureDifference β μ ν p^2‖≤4 := by
    rw [norm_pow];exact (pow_le_pow_left₀ (norm_nonneg _) hz 2).trans_eq (by norm_num)
  have h₂ : ‖2*(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p*
      parisiHessian β μ p*scalarGradientDifference β μ ν p‖≤4 := by
    simp only [norm_mul, Real.norm_ofNat]
    calc
      (2:ℝ) * ‖parisiCDF ν p.1-parisiCDF μ p.1‖ * ‖parisiGradient β μ p‖ * ‖parisiHessian β μ p‖ * ‖scalarGradientDifference β μ ν p‖ ≤ (2:ℝ)*1*1*1*2 := by gcongr
      _=4 := by norm_num
  have h₃ : ‖2*parisiCDF ν p.1*parisiHessian β μ p*scalarGradientDifference β μ ν p^2‖≤8 := by
    simp only [norm_mul,norm_pow,Real.norm_ofNat]
    calc
      (2:ℝ) * ‖parisiCDF ν p.1‖ * ‖parisiHessian β μ p‖ * ‖scalarGradientDifference β μ ν p‖^2 ≤ (2:ℝ)*1*1*2^2 := by gcongr
      _=8 := by norm_num
  have hA : ‖(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p+
      parisiCDF ν p.1*scalarGradientDifference β μ ν p‖≤3 := by
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul]
    calc
      ‖parisiCDF ν p.1-parisiCDF μ p.1‖ * ‖parisiGradient β μ p‖ + ‖parisiCDF ν p.1‖ * ‖scalarGradientDifference β μ ν p‖ ≤ (1:ℝ)*1+1*2 := by gcongr
      _=3 := by norm_num
  have h₄ : ‖2*((parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p+
      parisiCDF ν p.1*scalarGradientDifference β μ ν p)*
        scalarGradientDifference β μ ν p*scalarCurvatureDifference β μ ν p‖≤24 := by
    simp only [norm_mul, Real.norm_ofNat]
    calc
      (2:ℝ) * ‖(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p+parisiCDF ν p.1*scalarGradientDifference β μ ν p‖ * ‖scalarGradientDifference β μ ν p‖ * ‖scalarCurvatureDifference β μ ν p‖ ≤ (2:ℝ)*3*2*2 := by gcongr
      _=24 := by norm_num
  unfold scalarClippingSquareSource
  rw [norm_mul,Real.norm_of_nonneg (sq_nonneg β)]
  have htriangle (A B C D : ℝ) : ‖A-B-C-D‖≤‖A‖+‖B‖+‖C‖+‖D‖ := by
    exact ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans
      (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl)
  have hb : ‖scalarCurvatureDifference β μ ν p^2-
      2*(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p*parisiHessian β μ p*
        scalarGradientDifference β μ ν p-
      2*parisiCDF ν p.1*parisiHessian β μ p*scalarGradientDifference β μ ν p^2-
      2*((parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p+
        parisiCDF ν p.1*scalarGradientDifference β μ ν p)*
        scalarGradientDifference β μ ν p*scalarCurvatureDifference β μ ν p‖≤40 :=
    (htriangle _ _ _ _).trans (by linarith)
  exact (mul_le_mul_of_nonneg_left hb (sq_nonneg β)).trans_eq (by ring)

@[fun_prop] theorem measurable_scalarClippingPotentialSource (β : ℝ) (μ ν : Paper.ParisiMeasure) :
    Measurable (scalarClippingPotentialSource β μ ν) := by
  have hμ : Measurable (fun p : ℝ×ℝ=>parisiCDF μ p.1) :=
    (parisiCDF_measurable μ).comp measurable_fst
  have hν : Measurable (fun p : ℝ×ℝ=>parisiCDF ν p.1) :=
    (parisiCDF_measurable ν).comp measurable_fst
  have hM:=(continuous_parisiGradient β μ).measurable
  have hy:=(continuous_scalarGradientDifference β μ ν).measurable
  exact measurable_const.mul (((hν.sub hμ).mul (hM.pow_const 2)).add
    ((measurable_const.mul (hν.sub hμ)).mul hM |>.mul hy) |>.add (hν.mul (hy.pow_const 2)))

@[fun_prop] theorem measurable_scalarClippingSquareSource (β : ℝ) (μ ν : Paper.ParisiMeasure) :
    Measurable (scalarClippingSquareSource β μ ν) := by
  have hμ : Measurable (fun p : ℝ×ℝ=>parisiCDF μ p.1) :=
    (parisiCDF_measurable μ).comp measurable_fst
  have hν : Measurable (fun p : ℝ×ℝ=>parisiCDF ν p.1) :=
    (parisiCDF_measurable ν).comp measurable_fst
  have hM:=(continuous_parisiGradient β μ).measurable
  have hC:=(continuous_parisiHessian_all β μ).measurable
  have hy:=(continuous_scalarGradientDifference β μ ν).measurable
  have hz:=(continuous_scalarCurvatureDifference β μ ν).measurable
  exact measurable_const.mul (((hz.pow_const 2).sub
    (((measurable_const.mul (hν.sub hμ)).mul hM).mul hC |>.mul hy)).sub
      ((measurable_const.mul hν).mul hC |>.mul (hy.pow_const 2)) |>.sub
      (measurable_const.mul (((hν.sub hμ).mul hM).add (hν.mul hy)) |>.mul hy |>.mul hz))

end QuantitativeFollowup
