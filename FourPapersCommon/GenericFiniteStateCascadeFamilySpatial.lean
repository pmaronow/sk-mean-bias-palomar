module
public import FourPapersCommon.GenericFiniteStateCascadeFamilyContinuity

@[expose] public section

/-! Joint spatial derivative continuity for an actual time-dependent Gaussian
step. All continuity under the Gaussian expectation is proved by domination. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 800000
variable {S I : Type*} [Fintype S] [Fintype I]

theorem FiniteStateGaussianTimeData.lipschitz
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    LipschitzWith C (F t) :=
  lipschitzWith_of_nnnorm_fderiv_le ((d.spatial_C2 t ht).differentiable (by norm_num))
    (fun H => NNReal.coe_le_coe.mp (d.first_bound t ht H))

theorem continuousOn_finiteStateGaussian_family_denominator
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    ContinuousOn (fun p : ℝ×FiniteStateField S =>
      ∫ z, Real.exp (a*F p.1 (p.2+Real.sqrt (1-p.1) • L z))
        ∂stdGaussian (FiniteStateGaussianInput I)) (finiteStateGaussianTimeDomain S) := by
  simpa only [smul_eq_mul, mul_one] using
    continuousOn_weighted_finiteStateGaussian_family d a L (fun _ _ => (1 : ℝ))
      continuous_const.continuousOn 1 (fun _ _ _ => by simp)

theorem continuousOn_normalized_finiteStateGaussian_family
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (G : ℝ → FiniteStateField S → V)
    (hG : ContinuousOn (fun p : ℝ×FiniteStateField S => G p.1 p.2) (finiteStateGaussianTimeDomain S))
    (R : ℝ≥0) (hR : ∀ t ∈ Ioo 0 1, ∀ H, ‖G t H‖ ≤ R) :
    ContinuousOn (fun p : ℝ×FiniteStateField S =>
      (∫ z, Real.exp (a*F p.1 (p.2+Real.sqrt (1-p.1) • L z))
        ∂stdGaussian (FiniteStateGaussianInput I))⁻¹ •
      (∫ z, Real.exp (a*F p.1 (p.2+Real.sqrt (1-p.1) • L z)) •
        G p.1 (p.2+Real.sqrt (1-p.1) • L z) ∂stdGaussian (FiniteStateGaussianInput I)))
          (finiteStateGaussianTimeDomain S) := by
  have hc := continuousOn_finiteStateGaussian_family_denominator d a L
  have hp (p : ℝ×FiniteStateField S) (h : p ∈ finiteStateGaussianTimeDomain S) :
      (∫ z, Real.exp (a*F p.1 (p.2+Real.sqrt (1-p.1) • L z))
        ∂stdGaussian (FiniteStateGaussianInput I)) ≠ 0 :=
    (integral_exp_pos (integrable_exp_finiteStateGaussian_lipschitz (F p.1)
      (d.lipschitz p.1 h.1) (Real.sqrt (1-p.1) • L) p.2 a)).ne'
  exact (hc.inv₀ hp).smul (continuousOn_weighted_finiteStateGaussian_family d a L G hG R hR)

theorem continuousOn_finiteStateGaussian_family_differential
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    ContinuousOn (fun p : ℝ×FiniteStateField S =>
      finiteStateGaussianDifferential a (Real.sqrt (1-p.1) • L) (F p.1) p.2)
        (finiteStateGaussianTimeDomain S) := by
  simpa only [finiteStateGaussianDifferential, smul_apply] using
    continuousOn_normalized_finiteStateGaussian_family d a L
      (fun t H => fderiv ℝ (F t) H) d.first_cont C d.first_bound

theorem continuousOn_finiteStateGaussian_family_hessian
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    ContinuousOn (fun p : ℝ×FiniteStateField S =>
      finiteStateGaussianHessian a (Real.sqrt (1-p.1) • L) (F p.1) p.2)
        (finiteStateGaussianTimeDomain S) := by
  have hcSub : ContinuousSub (FiniteStateField S →L[ℝ] FiniteStateField S →L[ℝ] ℝ) :=
    @IsTopologicalAddGroup.to_continuousSub _ _ _ ContinuousLinearMap.isTopologicalAddGroup
  let G : ℝ → FiniteStateField S → (FiniteStateField S →L[ℝ] FiniteStateField S →L[ℝ] ℝ) :=
    fun t H => fderiv ℝ (fderiv ℝ (F t)) H +
    a • (fderiv ℝ (F t) H).smulRight (fderiv ℝ (F t) H)
  have hdyad : ContinuousOn (fun p : ℝ×FiniteStateField S =>
      (fderiv ℝ (F p.1) p.2).smulRight (fderiv ℝ (F p.1) p.2))
        (finiteStateGaussianTimeDomain S) :=
    (ContinuousLinearMap.smulRightL ℝ (FiniteStateField S)
      (FiniteStateField S →L[ℝ] ℝ)).continuous₂.comp_continuousOn
        (d.first_cont.prodMk d.first_cont)
  have hG : ContinuousOn (fun p : ℝ×FiniteStateField S => G p.1 p.2)
      (finiteStateGaussianTimeDomain S) := by
    exact d.second_cont.add (hdyad.const_smul a)
  let R : ℝ≥0 := Real.toNNReal (B+|a| *C^2)
  have hRco : (R : ℝ) = B+|a| *C^2 := Real.coe_toNNReal _ (by positivity)
  have hR (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) : ‖G t H‖ ≤ R := by
    rw [hRco]
    apply (ContinuousLinearMap.opNorm_add_le _ _).trans
    have hs : ‖a • (fderiv ℝ (F t) H).smulRight (fderiv ℝ (F t) H)‖ ≤
        |a| *(‖fderiv ℝ (F t) H‖*‖fderiv ℝ (F t) H‖) := by
      convert ContinuousLinearMap.opNorm_smul_le a
        ((fderiv ℝ (F t) H).smulRight (fderiv ℝ (F t) H)) using 1
      simp only [Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
    have hh := mul_le_mul (d.first_bound t ht H) (d.first_bound t ht H) (norm_nonneg _) C.2
    have ha := mul_le_mul_of_nonneg_left hh (abs_nonneg a)
    nlinarith [d.second_bound t ht H, hs]
  have hw := continuousOn_normalized_finiteStateGaussian_family d a L G hG R hR
  have hd := continuousOn_finiteStateGaussian_family_differential d a L
  have hdd : ContinuousOn (fun p : ℝ×FiniteStateField S =>
      (finiteStateGaussianDifferential a (Real.sqrt (1-p.1) • L) (F p.1) p.2).smulRight
        (finiteStateGaussianDifferential a (Real.sqrt (1-p.1) • L) (F p.1) p.2))
          (finiteStateGaussianTimeDomain S) :=
    (ContinuousLinearMap.smulRightL ℝ (FiniteStateField S)
      (FiniteStateField S →L[ℝ] ℝ)).continuous₂.comp_continuousOn (hd.prodMk hd)
  convert @ContinuousOn.sub _ _ _ _ _ hcSub _ _ _ hw (hdd.const_smul a) using 1
  rfl

end FourPapersCommon
