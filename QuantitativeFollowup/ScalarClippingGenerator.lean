module
public import QuantitativeFollowup.ScalarClippingFields
public import FRSB.BackwardsParity

@[expose] public section

/-! Literal generator identities for the actual difference of two scalar
PDE solutions, and its squared gradient difference. These are the analytic
sources in the fifth-order clipping argument. -/
noncomputable section
open Set Paper FRSB
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 600000

def scalarGradientDifference (β : ℝ) (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) : ℝ :=
  parisiGradient β ν p-parisiGradient β μ p

def scalarCurvatureDifference (β : ℝ) (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) : ℝ :=
  parisiHessian β ν p-parisiHessian β μ p

def scalarClippingPotentialSource (β : ℝ) (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) : ℝ :=
  -(β^2/2)*((parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p^2+
    2*(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p*
      scalarGradientDifference β μ ν p+
    parisiCDF ν p.1*scalarGradientDifference β μ ν p^2)

def scalarClippingSquareSource (β : ℝ) (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) : ℝ :=
  β^2*(scalarCurvatureDifference β μ ν p^2-
    2*(parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p*
      parisiHessian β μ p*scalarGradientDifference β μ ν p-
    2*parisiCDF ν p.1*parisiHessian β μ p*scalarGradientDifference β μ ν p^2-
    2*((parisiCDF ν p.1-parisiCDF μ p.1)*parisiGradient β μ p+
      parisiCDF ν p.1*scalarGradientDifference β μ ν p)*
        scalarGradientDifference β μ ν p*scalarCurvatureDifference β μ ν p)

theorem scalarClippingPotentialSource_eq_generator (β : ℝ) (μ ν : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    parisiTimeField β ν 0 (t,x)-parisiTimeField β μ 0 (t,x)+
      scalarGradientDifference β μ ν (t,x)*(β^2*parisiCDF μ t*parisiGradient β μ (t,x))+
      (1/2:ℝ)*scalarCurvatureDifference β μ ν (t,x)*β^2=
        scalarClippingPotentialSource β μ ν (t,x) := by
  have hμ : parisiSpatialField β μ 2 (t,x)=parisiHessian β μ (t,x) :=
    backwardC_eq_hessian β μ t x ht
  have hν : parisiSpatialField β ν 2 (t,x)=parisiHessian β ν (t,x) :=
    backwardC_eq_hessian β ν t x ht
  unfold parisiTimeField scalarClippingPotentialSource scalarGradientDifference scalarCurvatureDifference
  rw [parisiSquareSpatialField_zero,parisiSquareSpatialField_zero,hμ,hν]
  ring

theorem scalarClippingSquareSource_eq_generator (β : ℝ) (μ ν : Paper.ParisiMeasure)
    (t x : ℝ) :
    2*scalarGradientDifference β μ ν (t,x)*
        (parisiTimeField β ν 1 (t,x)-parisiTimeField β μ 1 (t,x))+
      (2*scalarGradientDifference β μ ν (t,x)*scalarCurvatureDifference β μ ν (t,x))*
        (β^2*parisiCDF μ t*parisiGradient β μ (t,x))+
      (1/2:ℝ)*(2*scalarCurvatureDifference β μ ν (t,x)^2+
        2*scalarGradientDifference β μ ν (t,x)*
          (parisiSpatialField β ν 3 (t,x)-parisiSpatialField β μ 3 (t,x)))*β^2=
        scalarClippingSquareSource β μ ν (t,x) := by
  unfold parisiTimeField
  rw [parisiSquareSpatialField_one_eq,parisiSquareSpatialField_one_eq]
  unfold scalarClippingSquareSource scalarGradientDifference scalarCurvatureDifference
  ring

theorem norm_scalarGradientDifference_le (β : ℝ) (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) :
    ‖scalarGradientDifference β μ ν p‖≤2 :=
  (norm_sub_le _ _).trans (by linarith [norm_parisiGradient_le_one β μ p,
    norm_parisiGradient_le_one β ν p])

theorem norm_scalarCurvatureDifference_le (β : ℝ) (μ ν : Paper.ParisiMeasure) (p : ℝ×ℝ) :
    ‖scalarCurvatureDifference β μ ν p‖≤2 :=
  (norm_sub_le _ _).trans (by linarith [norm_parisiHessian_le_one_all β μ p,
    norm_parisiHessian_le_one_all β ν p])

theorem scalarClippingSquareSource_energy_le (β : ℝ) (μ ν : Paper.ParisiMeasure)
    (p : ℝ×ℝ) (ht : p.1∈Icc (0:ℝ) 1) (hv : parisiCDF μ p.1≤parisiCDF ν p.1) :
    -scalarClippingSquareSource β μ ν p≤β^2*(
      11*scalarGradientDifference β μ ν p^2+
      2*(parisiCDF ν p.1-parisiCDF μ p.1)*|parisiGradient β μ p| *
        |scalarGradientDifference β μ ν p|) := by
  let v:=parisiCDF ν p.1-parisiCDF μ p.1
  let M:=parisiGradient β μ p
  let C:=parisiHessian β μ p
  let y:=scalarGradientDifference β μ ν p
  let z:=scalarCurvatureDifference β μ ν p
  let b:=parisiCDF ν p.1
  let A:=v*M+b*y
  have hv0 : 0≤v := sub_nonneg.mpr hv
  have hv1 : v≤1 := by dsimp [v];linarith [parisiCDF_le_one ν p.1,parisiCDF_nonneg μ p.1]
  have hM : |M|≤1 := by simpa only [M,←Real.norm_eq_abs] using norm_parisiGradient_le_one β μ p
  have hy : |y|≤2 := by simpa only [y,←Real.norm_eq_abs] using norm_scalarGradientDifference_le β μ ν p
  have hC0 : 0≤C := (parisiHessian_pos_all β μ p.1 p.2 ht).le
  have hC1 : C≤1 := parisiHessian_le_one_all β μ p
  have hb0 : 0≤b := parisiCDF_nonneg ν p.1
  have hb1 : b≤1 := parisiCDF_le_one ν p.1
  have hA : |A|≤3 := by
    dsimp only [A]
    calc
      _≤|v*M|+|b*y| := abs_add_le _ _
      _=v*|M|+b*|y| := by rw [abs_mul,abs_mul,abs_of_nonneg hv0,abs_of_nonneg hb0]
      _≤1*1+1*2 := add_le_add (mul_le_mul hv1 hM (abs_nonneg _) zero_le_one)
        (mul_le_mul hb1 hy (abs_nonneg _) zero_le_one)
      _=3 := by norm_num
  have hA2 : A^2≤9 := by nlinarith [abs_le.mp hA,sq_abs A]
  have hcross : 2*v*M*C*y≤2*v*|M| *|y| := by
    have hh : M*C*y≤|M| *|y| := by
      calc
        _≤|M*C*y| := le_abs_self _
        _=|M| *C*|y| := by rw [abs_mul,abs_mul,abs_of_nonneg hC0]
        _≤|M| *1*|y| := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hC1 (abs_nonneg M)) (abs_nonneg y)
        _=|M| *|y| := by ring
    nlinarith [mul_le_mul_of_nonneg_left hh (mul_nonneg (by norm_num : (0:ℝ)≤2) hv0)]
  have hreact : 2*b*C*y^2≤2*y^2 := by
    have hh : b*C≤1 := (mul_le_mul hb1 hC1 hC0 zero_le_one).trans_eq (one_mul _)
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg y)]
  have hyoung : -z^2+2*A*y*z≤9*y^2 := by
    have hh : -z^2+2*A*y*z≤A^2*y^2 := by nlinarith [sq_nonneg (z-A*y)]
    exact hh.trans (mul_le_mul_of_nonneg_right hA2 (sq_nonneg y))
  unfold scalarClippingSquareSource
  change -(β^2*(z^2-2*v*M*C*y-2*b*C*y^2-2*A*y*z))≤_
  have hh : -(z^2-2*v*M*C*y-2*b*C*y^2-2*A*y*z)≤
      11*y^2+2*v*|M| *|y| := by linarith
  convert mul_le_mul_of_nonneg_left hh (sq_nonneg β) using 1 <;> ring

end QuantitativeFollowup
