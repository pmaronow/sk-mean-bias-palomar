module
public import FourPapersCommon.GenericFiniteStateCascadeTimeNormalization

@[expose] public section

/-! Integrability of the actual linear-growth observables under Gaussian
exponential tilts. This permits linearity in the varying-prior time formula. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 500000
variable {S I : Type*} [Fintype S] [Fintype I]

theorem integrable_finiteStateGaussian_tilt_linear_growth
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) {C : ℝ≥0} (hF : LipschitzWith C F)
    (H : FiniteStateField S) (D : FiniteStateGaussianInput I → ℝ)
    (hD : Measurable D) (M N : ℝ≥0) (hb : ∀ z, |D z| ≤ M+N*‖z‖) :
    Integrable D ((stdGaussian (FiniteStateGaussianInput I)).tilted
      (fun z => a*F (H+L z))) := by
  apply (integrable_tilted_iff (integrable_exp_finiteStateGaussian_lipschitz F hF L H a) D).2
  let c := |a| *C*‖L‖
  have hExp (z : FiniteStateGaussianInput I) : Real.exp (a*F (H+L z)) ≤
      Real.exp (a*F H)*Real.exp (c*‖z‖) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hh := hF.norm_sub_le (H+L z) H
    simp only [Real.norm_eq_abs, add_sub_cancel_left] at hh
    have hmul := mul_le_mul_of_nonneg_left
      (hh.trans (mul_le_mul_of_nonneg_left (L.le_opNorm z) C.2)) (abs_nonneg a)
    have ha := le_abs_self (a*(F (H+L z)-F H))
    rw [abs_mul] at ha
    dsimp [c]
    nlinarith
  have hbound (z : FiniteStateGaussianInput I) :
      ‖Real.exp (a*F (H+L z)) • D z‖ ≤
        ((M+N)*Real.exp (a*F H))*Real.exp ((c+1)*‖z‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hn : ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
    have h1 : (1 : ℝ) ≤ Real.exp ‖z‖ := Real.one_le_exp (norm_nonneg z)
    have hD' : |D z| ≤ (M+N)*Real.exp ‖z‖ :=
      (hb z).trans (by nlinarith [mul_le_mul_of_nonneg_left h1 M.2,
        mul_le_mul_of_nonneg_left hn N.2])
    have hh := mul_le_mul (hExp z) hD' (abs_nonneg _) (by positivity)
    calc
      _ ≤ (Real.exp (a*F H)*Real.exp (c*‖z‖))*((M+N)*Real.exp ‖z‖) := hh
      _ = _ := by
        rw [show (c+1)*‖z‖ = c*‖z‖+‖z‖ by ring, Real.exp_add]
        ring
  refine ((integrable_exp_mul_norm_gaussian (stdGaussian (FiniteStateGaussianInput I)) (c+1)).const_mul
    ((M+N)*Real.exp (a*F H))).mono' ?_ (.of_forall hbound)
  exact ((Real.continuous_exp.comp ((hF.continuous.comp
    (continuous_const.add L.continuous)).const_mul a)).measurable.smul hD).aestronglyMeasurable

theorem finiteStateGaussianInputMean_sub (a : ℝ)
    (F D E : FiniteStateGaussianInput I → ℝ)
    (hF : Measurable F) (hD : Measurable D) (hE : Measurable E)
    (hiD : Integrable D ((stdGaussian (FiniteStateGaussianInput I)).tilted (fun z => a*F z)))
    (hiE : Integrable E ((stdGaussian (FiniteStateGaussianInput I)).tilted (fun z => a*F z))) :
    finiteStateGaussianInputMean a F (fun z => D z-E z) =
      finiteStateGaussianInputMean a F D-finiteStateGaussianInputMean a F E := by
  have hsub : Measurable (fun z => D z-E z) := hD.sub hE
  rw [finiteStateGaussianInputMean_eq_integral_tilted a F (fun z => D z-E z) hF hsub,
    finiteStateGaussianInputMean_eq_integral_tilted a F D hF hD,
    finiteStateGaussianInputMean_eq_integral_tilted a F E hF hE,
    integral_sub hiD hiE]

end FourPapersCommon
