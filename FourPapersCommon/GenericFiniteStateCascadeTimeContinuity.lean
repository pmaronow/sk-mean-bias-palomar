module
public import FourPapersCommon.GenericFiniteStateCascadeGeneratorMean

@[expose] public section

/-! Joint continuity and uniform bounds for the actual interpolated-step time
derivative, proved from the inherited finite-state derivatives. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 500000
variable {S I : Type*} [Fintype S] [Fintype I]

theorem abs_integral_finiteStateGaussianStepLaw_le (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) {C : ℝ≥0} (hF : LipschitzWith C F)
    (G : FiniteStateField S → ℝ) (H : FiniteStateField S) (R : ℝ≥0)
    (hb : ∀ y, |G y| ≤ R) :
    |∫ y, G y ∂finiteStateGaussianStepLaw a L F H| ≤ R := by
  have := isProbabilityMeasure_finiteStateGaussianStepLaw a L F hF.continuous.measurable H
    (integrable_exp_finiteStateGaussian_lipschitz F hF L H a)
  have hh := norm_integral_le_of_norm_le (f := G)
    (integrable_const (R : ℝ) : Integrable (fun _ => (R : ℝ))
      (finiteStateGaussianStepLaw a L F H)) (.of_forall fun y => by simpa only [Real.norm_eq_abs] using hb y)
  simpa using hh

theorem continuousOn_finiteStateGaussian_family_stepMean
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (G : ℝ → FiniteStateField S → ℝ)
    (hG : ContinuousOn (fun p : ℝ×FiniteStateField S => G p.1 p.2) (finiteStateGaussianTimeDomain S))
    (R : ℝ≥0) (hR : ∀ t ∈ Ioo 0 1, ∀ H, |G t H| ≤ R) :
    ContinuousOn (fun p : ℝ×FiniteStateField S =>
      ∫ y, G p.1 y ∂finiteStateGaussianStepLaw a (Real.sqrt (1-p.1) • L) (F p.1) p.2)
        (finiteStateGaussianTimeDomain S) := by
  have hc := continuousOn_normalized_finiteStateGaussian_family d a L G hG R
    (fun t ht H => by simpa only [Real.norm_eq_abs] using hR t ht H)
  apply hc.congr
  intro p hp
  have hGc : Continuous (G p.1) := continuousOn_univ.mp
    (hG.comp (continuous_const.prodMk continuous_id).continuousOn (fun y _ => ⟨hp.1,mem_univ y⟩))
  exact (integral_finiteStateGaussianStepLaw a _ (F p.1) (d.spatial_C2 p.1 hp.1).continuous.measurable
    (G p.1) hGc.stronglyMeasurable p.2)

theorem continuousOn_finiteStateGaussianPriorTimeMean
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    ContinuousOn (fun p : ℝ×FiniteStateField S => finiteStateGaussianPriorTimeMean d a L p.1 p.2)
      (finiteStateGaussianTimeDomain S) := by
  apply (continuousOn_finiteStateGaussian_family_stepMean d a L d.time d.time_cont K d.time_bound).congr
  intro p hp
  change finiteStateGaussianPriorTimeMean d a L p.1 p.2 = _
  have hTc : Continuous (d.time p.1) := continuousOn_univ.mp
    (d.time_cont.comp (continuous_const.prodMk continuous_id).continuousOn (fun y _ => ⟨hp.1,mem_univ y⟩))
  exact (finiteStateGaussianInputMean_field_eq_stepLaw a (1-p.1) L (F p.1) (d.time p.1)
    (d.spatial_C2 p.1 hp.1).continuous.measurable hTc.measurable p.2)

theorem abs_finiteStateGaussianPriorTimeMean_le
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    |finiteStateGaussianPriorTimeMean d a L t H| ≤ K := by
  have hTc : Continuous (d.time t) := continuousOn_univ.mp
    (d.time_cont.comp (continuous_const.prodMk continuous_id).continuousOn (fun y _ => ⟨ht,mem_univ y⟩))
  rw [finiteStateGaussianPriorTimeMean, finiteStateGaussianInputMean_field_eq_stepLaw a (1-t) L
    (F t) (d.time t) (d.spatial_C2 t ht).continuous.measurable hTc.measurable H]
  exact abs_integral_finiteStateGaussianStepLaw_le a _ (F t) (d.lipschitz t ht) (d.time t) H K (d.time_bound t ht)

theorem abs_finiteStateGaussianVarianceGenerator_le (a v : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) (H : FiniteStateField S) :
    |finiteStateGaussianVarianceGenerator a v L F H| ≤ finiteStateGaussianGeneratorBound a L C B := by
  rw [finiteStateGaussianVarianceGenerator_eq_stepMean a v L F hF C B hC hB H]
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le
    (hF.differentiable (by norm_num)) (fun y => NNReal.coe_le_coe.mp (hC y))
  exact abs_integral_finiteStateGaussianStepLaw_le a _ F hLip _ H _
    (abs_finiteStateGaussianGeneratorField_le a L F C B hC hB)

end FourPapersCommon
