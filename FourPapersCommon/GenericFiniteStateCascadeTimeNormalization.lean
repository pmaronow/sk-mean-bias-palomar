module
public import FourPapersCommon.GenericFiniteStateCascadeRawTime

@[expose] public section

/-! The raw Gaussian gradient term is identified with the actual variance
generator by uniqueness of two independently justified derivatives. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 800000
variable {S I : Type*} [Fintype S] [Fintype I]

def finiteStateGaussianConstantTimeData
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) :
    FiniteStateGaussianTimeData (fun _ => F) C B 0 where
  time := fun _ _ => 0
  cont := (hF.continuous.comp continuous_snd).continuousOn
  first_cont := ((hF.continuous_fderiv (by norm_num)).comp continuous_snd).continuousOn
  second_cont := (((hF.fderiv_right (m := (1 : ℕ∞ω)) (by norm_num)).continuous_fderiv
    (by norm_num)).comp continuous_snd).continuousOn
  spatial_C2 := fun _ _ => hF
  first_bound := fun _ _ => hC
  second_bound := fun _ _ => hB
  time_cont := continuous_const.continuousOn
  time_hasDeriv := fun t _ H => hasDerivAt_const t (F H)
  time_bound := fun _ _ _ => by simp

theorem finiteStateGaussianInputMean_const_mul (a c : ℝ)
    (F D : FiniteStateGaussianInput I → ℝ) :
    finiteStateGaussianInputMean a F (fun z => c*D z) =
      c*finiteStateGaussianInputMean a F D := by
  simp only [finiteStateGaussianInputMean, SpinGlass.Targets.pairedTiltMean]
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

theorem finiteStateGaussianInputMean_raw_gradient_eq_variance
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B)
    (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    finiteStateGaussianInputMean a
      (fun z => F (H+Real.sqrt (1-t) • L z))
      (fun z => fderiv ℝ F (H+Real.sqrt (1-t) • L z) (L z)/(2*Real.sqrt (1-t))) =
        finiteStateGaussianVarianceGenerator a (1-t) L F H := by
  let d := finiteStateGaussianConstantTimeData F hF C B hC hB
  have hraw := hasDerivAt_finiteStateGaussianStep_time_raw d a L t ht H
  have hvar := (hasDerivAt_finiteStateGaussianStep_variance a L F hF C B hC hB H
    (sub_pos.mpr ht.2)).comp t ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  have he := hraw.unique hvar
  have hn : finiteStateGaussianShiftedTime d L t H =
      fun z => (-1 : ℝ)*(fderiv ℝ F (H+Real.sqrt (1-t) • L z) (L z)/(2*Real.sqrt (1-t))) := by
    funext z
    simp [finiteStateGaussianShiftedTime, d, finiteStateGaussianConstantTimeData]
  rw [hn, finiteStateGaussianInputMean_const_mul] at he
  simpa only [zero_sub, mul_neg_one, neg_mul, one_mul, neg_inj] using he

end FourPapersCommon
