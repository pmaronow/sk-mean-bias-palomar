module
public import FourPapersCommon.FiniteStatePosteriorCoordinateTowerDefinitions

@[expose] public section

/-! A uniform, genuine integrable envelope for a normalized Gaussian input
under a Lipschitz potential. The envelope is independent of the parent field. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal
namespace FourPapersCommon
set_option maxHeartbeats 800000
variable {S I : Type*} [Fintype S] [Fintype I]

def posteriorCoordinateGaussianLower (I : Type*) [Fintype I] (c : ℝ) : ℝ :=
  ∫z,Real.exp (-c*‖z‖) ∂stdGaussian (FiniteStateGaussianInput I)

theorem posteriorCoordinateGaussianLower_pos (c : ℝ) :
    0<posteriorCoordinateGaussianLower I c :=
  integral_exp_pos (integrable_exp_mul_norm_gaussian (stdGaussian (FiniteStateGaussianInput I)) (-c))

theorem posteriorCoordinateGaussian_density_bound
    (mass : ℝ) (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (F : FiniteStateField S→ℝ) {C : ℝ≥0} (hF : LipschitzWith C F)
    (H : FiniteStateField S) (z : FiniteStateGaussianInput I) :
    Real.exp (mass*F (H+L z))/(∫w,Real.exp (mass*F (H+L w)) ∂stdGaussian (FiniteStateGaussianInput I))≤
      Real.exp ((|mass| *C*‖L‖)*‖z‖)/posteriorCoordinateGaussianLower I (|mass| *C*‖L‖) := by
  let c := |mass| *C*‖L‖
  have hab (w : FiniteStateGaussianInput I) : |mass*(F (H+L w)-F H)|≤c*‖w‖ := by
    rw [abs_mul]
    have hh:=hF.norm_sub_le (H+L w) H
    simp only [Real.norm_eq_abs,add_sub_cancel_left] at hh
    have hu:=mul_le_mul_of_nonneg_left
      (hh.trans (mul_le_mul_of_nonneg_left (L.le_opNorm w) C.2)) (abs_nonneg mass)
    simpa only [c,mul_assoc] using hu
  have hupper (w : FiniteStateGaussianInput I) :
      Real.exp (mass*F (H+L w))≤Real.exp (mass*F H)*Real.exp (c*‖w‖) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [(le_abs_self _).trans (hab w)]
  have hlower (w : FiniteStateGaussianInput I) :
      Real.exp (mass*F H)*Real.exp (-c*‖w‖)≤Real.exp (mass*F (H+L w)) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [neg_abs_le (mass*(F (H+L w)-F H)),hab w]
  have hz : Real.exp (mass*F H)*posteriorCoordinateGaussianLower I c≤
      ∫w,Real.exp (mass*F (H+L w)) ∂stdGaussian (FiniteStateGaussianInput I) := by
    rw [posteriorCoordinateGaussianLower,←integral_const_mul]
    exact integral_mono
      ((integrable_exp_mul_norm_gaussian (stdGaussian (FiniteStateGaussianInput I)) (-c)).const_mul _)
      (integrable_exp_finiteStateGaussian_lipschitz F hF L H mass) hlower
  have hp:=posteriorCoordinateGaussianLower_pos (I:=I) c
  calc
    _ ≤ (Real.exp (mass*F H)*Real.exp (c*‖z‖))/
        (Real.exp (mass*F H)*posteriorCoordinateGaussianLower I c) :=
      div_le_div₀ (by positivity) (hupper z) (mul_pos (Real.exp_pos _) hp) hz
    _ = _ := by dsimp only [c];field_simp

/-- A dimension-dependent integrable Gaussian envelope, valid at every
parent field, controls the absolute raw input coordinate. -/
theorem posteriorCoordinateGaussian_coordinate_envelope
    (mass : ℝ) (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (F : FiniteStateField S→ℝ) {C : ℝ≥0} (hF : LipschitzWith C F)
    (H : FiniteStateField S) (z : FiniteStateGaussianInput I) (i : Fin (Fintype.card I)) :
    (Real.exp (mass*F (H+L z))/(∫w,Real.exp (mass*F (H+L w)) ∂stdGaussian (FiniteStateGaussianInput I)))*
      |(finiteStateGaussianBasis I).repr z i|≤
      Real.exp ((|mass| *C*‖L‖+1)*‖z‖)/posteriorCoordinateGaussianLower I (|mass| *C*‖L‖) := by
  have h1 : ‖z‖≤Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
  have hc := (abs_finiteStateGaussianInput_coordinate_le i z).trans h1
  have hp:=posteriorCoordinateGaussianLower_pos (I:=I) (|mass| *C*‖L‖)
  have hh:=mul_le_mul (posteriorCoordinateGaussian_density_bound mass L F hF H z) hc
    (abs_nonneg _) (by positivity : 0≤Real.exp ((|mass| *C*‖L‖)*‖z‖)/
      posteriorCoordinateGaussianLower I (|mass| *C*‖L‖))
  apply hh.trans_eq
  rw [show (|mass| *C*‖L‖+1)*‖z‖=(|mass| *C*‖L‖)*‖z‖+‖z‖ by ring,Real.exp_add]
  ring

end FourPapersCommon
