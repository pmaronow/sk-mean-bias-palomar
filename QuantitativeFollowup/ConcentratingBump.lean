module
public import FourPapersCommon.GaussianCurvatureCutoff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

@[expose] public section

/-! The literal quartic concentrating bump is a translated audited C1
cutoff. Its derivative and the exact area and Dirichlet energy follow
from actual derivatives and polynomial antiderivatives. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

def concentratingBump (y : ℝ) : ℝ := FourPapersCommon.curvatureCutoffUnit (2*y-1)
def concentratingBumpDerivative (y : ℝ) : ℝ :=
  2*FourPapersCommon.curvatureCutoffUnitDerivative (2*y-1)

theorem concentratingBump_eq_on_unit (y : ℝ) (hy : y∈Icc (0 : ℝ) 1) :
    concentratingBump y=16*y^2*(1-y)^2 := by
  have ht : |2*y-1|≤1 := abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩
  rw [concentratingBump,FourPapersCommon.curvatureCutoffUnit,ite_eq_left ht]
  ring

theorem concentratingBump_zero_outside (y : ℝ) (hy : y∉Ioo (0 : ℝ) 1) :
    concentratingBump y=0 := by
  by_cases hunit : y∈Icc (0 : ℝ) 1
  · rw [concentratingBump_eq_on_unit y hunit]
    have he : y=0 ∨ y=1 := by
      by_cases hzero : y=0
      · exact Or.inl hzero
      · right
        have hy0 : 0<y := lt_of_le_of_ne hunit.1 (Ne.symm hzero)
        exact le_antisymm hunit.2 (le_of_not_gt (fun hh => hy ⟨hy0,hh⟩))
    rcases he with rfl | rfl <;> norm_num
  · have ht : ¬|2*y-1|≤1 := by
      intro h
      have hh := abs_le.mp h
      exact hunit ⟨by linarith [hh.1],by linarith [hh.2]⟩
    simp only [concentratingBump,FourPapersCommon.curvatureCutoffUnit,ite_eq_right ht]

theorem concentratingBump_nonneg_le_one (y : ℝ) :
    0≤concentratingBump y ∧ concentratingBump y≤1 :=
  FourPapersCommon.curvatureCutoffUnit_bounds _

theorem contDiff_concentratingBump : ContDiff ℝ 1 concentratingBump :=
  FourPapersCommon.contDiff_curvatureCutoffUnit.comp
    (by fun_prop : ContDiff ℝ 1 (fun y : ℝ => 2*y-1))

theorem hasDerivAt_concentratingBump (y : ℝ) :
    HasDerivAt concentratingBump (concentratingBumpDerivative y) y := by
  have hd := (FourPapersCommon.hasDerivAt_curvatureCutoffUnit (2*y-1)).comp y
    (((hasDerivAt_id y).const_mul 2).sub_const 1)
  convert hd using 1
  · funext z
    dsimp only [concentratingBump,Function.comp_def,id_eq]
  · dsimp only [concentratingBumpDerivative]
    ring

theorem deriv_concentratingBump : deriv concentratingBump=concentratingBumpDerivative :=
  funext fun y => (hasDerivAt_concentratingBump y).deriv

theorem concentratingBumpDerivative_eq_on_unit (y : ℝ) (hy : y∈Icc (0 : ℝ) 1) :
    concentratingBumpDerivative y=32*y*(1-y)*(1-2*y) := by
  have ht : 0≤1-(2*y-1)^2 := by nlinarith [mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]
  rw [concentratingBumpDerivative,FourPapersCommon.curvatureCutoffUnitDerivative,max_eq_right ht]
  ring

theorem concentratingBumpDerivative_bound (y : ℝ) :
    |concentratingBumpDerivative y|≤4 := by
  rw [concentratingBumpDerivative,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  nlinarith [FourPapersCommon.curvatureCutoffUnit_derivative_bound (2*y-1)]

theorem concentratingBump_integral : (∫y in (0 : ℝ)..1,concentratingBump y)=8/15 := by
  let P : ℝ → ℝ := fun y => 16*(y^3/3-y^4/2+y^5/5)
  have hP (y : ℝ) : HasDerivAt P (16*y^2*(1-y)^2) y := by
    have hd := ((((hasDerivAt_id y).pow 3).div_const 3).sub
      (((hasDerivAt_id y).pow 4).div_const 2)).add
        (((hasDerivAt_id y).pow 5).div_const 5) |>.const_mul 16
    convert hd using 1
    · funext z
      dsimp only [P,Pi.sub_apply,Pi.add_apply,Pi.pow_apply,id_eq]
    · dsimp only [id_eq]
      norm_num
      ring
  have hi : IntervalIntegrable (fun y : ℝ => 16*y^2*(1-y)^2) volume 0 1 :=
    (by fun_prop : Continuous (fun y : ℝ => 16*y^2*(1-y)^2)).intervalIntegrable 0 1
  have he : (∫y in (0 : ℝ)..1,concentratingBump y)=∫y in (0 : ℝ)..1,16*y^2*(1-y)^2 :=
    intervalIntegral.integral_congr fun y hy => concentratingBump_eq_on_unit y
      (by simpa only [uIcc_of_le zero_le_one] using hy)
  rw [he,intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hP y) hi]
  norm_num [P]

theorem concentratingBump_energy :
    (∫y in (0 : ℝ)..1,(deriv concentratingBump y)^2)=512/105 := by
  let P : ℝ → ℝ := fun y => (1024/3)*y^3-1536*y^4+(13312/5)*y^5-2048*y^6+(4096/7)*y^7
  have hP (y : ℝ) : HasDerivAt P ((32*y*(1-y)*(1-2*y))^2) y := by
    have hd := (((((hasDerivAt_id y).pow 3).const_mul (1024/3)).sub
      (((hasDerivAt_id y).pow 4).const_mul 1536)).add
        (((hasDerivAt_id y).pow 5).const_mul (13312/5))).sub
          (((hasDerivAt_id y).pow 6).const_mul 2048) |>.add
            (((hasDerivAt_id y).pow 7).const_mul (4096/7))
    convert hd using 1
    · funext z
      dsimp only [P,Pi.sub_apply,Pi.add_apply,Pi.pow_apply,id_eq]
    · dsimp only [id_eq]
      norm_num
      ring
  have hi : IntervalIntegrable (fun y : ℝ => (32*y*(1-y)*(1-2*y))^2) volume 0 1 :=
    (by fun_prop : Continuous (fun y : ℝ => (32*y*(1-y)*(1-2*y))^2)).intervalIntegrable 0 1
  have he : (∫y in (0 : ℝ)..1,(deriv concentratingBump y)^2)=
      ∫y in (0 : ℝ)..1,(32*y*(1-y)*(1-2*y))^2 := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [deriv_concentratingBump]
    change (concentratingBumpDerivative y)^2=(32*y*(1-y)*(1-2*y))^2
    rw [concentratingBumpDerivative_eq_on_unit y (by simpa only [uIcc_of_le zero_le_one] using hy)]
  rw [he,intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hP y) hi]
  norm_num [P]

end QuantitativeFollowup
