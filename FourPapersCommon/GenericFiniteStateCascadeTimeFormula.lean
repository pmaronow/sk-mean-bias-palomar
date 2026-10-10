module
public import FourPapersCommon.GenericFiniteStateCascadeTiltIntegrability

@[expose] public section

/-! The actual covariance-interpolation derivative separates the preceding
time derivative from the genuine Gaussian variance generator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 500000
variable {S I : Type*} [Fintype S] [Fintype I]

def finiteStateGaussianPriorTimeMean
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (t : ℝ) (H : FiniteStateField S) : ℝ :=
  finiteStateGaussianInputMean a
    (fun z => F t (H+Real.sqrt (1-t) • L z))
    (fun z => d.time t (H+Real.sqrt (1-t) • L z))

theorem hasDerivAt_finiteStateGaussianStep_time
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    HasDerivAt (fun u => finiteStateGaussianStep a (Real.sqrt (1-u) • L) (F u) H)
      (finiteStateGaussianPriorTimeMean d a L t H-
        finiteStateGaussianVarianceGenerator a (1-t) L (F t) H) t := by
  let A := fun z : FiniteStateGaussianInput I => F t (H+Real.sqrt (1-t) • L z)
  let D := fun z : FiniteStateGaussianInput I => d.time t (H+Real.sqrt (1-t) • L z)
  let E := fun z : FiniteStateGaussianInput I =>
    fderiv ℝ (F t) (H+Real.sqrt (1-t) • L z) (L z)/(2*Real.sqrt (1-t))
  have hmap : Continuous (fun z : FiniteStateGaussianInput I => H+Real.sqrt (1-t) • L z) :=
    continuous_const.add (L.continuous.const_smul (Real.sqrt (1-t)))
  have hA : Measurable A := ((d.spatial_C2 t ht).continuous.comp hmap).measurable
  have htC : Continuous (d.time t) := continuousOn_univ.mp
    (d.time_cont.comp (continuous_const.prodMk continuous_id).continuousOn (fun y _ => ⟨ht,mem_univ y⟩))
  have hD : Measurable D := (htC.comp hmap).measurable
  have hE : Measurable E :=
    (((d.spatial_C2 t ht).continuous_fderiv (by norm_num)).comp hmap |>.clm_apply L.continuous
      |>.div_const (2*Real.sqrt (1-t))).measurable
  have hLip : LipschitzWith C (F t) := lipschitzWith_of_nnnorm_fderiv_le
    ((d.spatial_C2 t ht).differentiable (by norm_num))
      (fun y => NNReal.coe_le_coe.mp (d.first_bound t ht y))
  have hiD : Integrable D ((stdGaussian (FiniteStateGaussianInput I)).tilted (fun z => a*A z)) :=
    integrable_finiteStateGaussian_tilt_linear_growth a (Real.sqrt (1-t) • L) (F t) hLip H D hD K 0
      (fun z => by simpa only [NNReal.coe_zero, zero_mul, add_zero] using d.time_bound t ht _)
  let N : ℝ≥0 := Real.toNNReal (C*‖L‖/(2*Real.sqrt (1-t)))
  have hden : 0 < 2*Real.sqrt (1-t) := mul_pos (by norm_num) (Real.sqrt_pos.2 (sub_pos.mpr ht.2))
  have hN : (N : ℝ) = C*‖L‖/(2*Real.sqrt (1-t)) := Real.coe_toNNReal _ (by positivity)
  have hbE (z : FiniteStateGaussianInput I) : |E z| ≤ (0 : ℝ≥0)+N*‖z‖ := by
    have hh := (fderiv ℝ (F t) (H+Real.sqrt (1-t) • L z)).le_opNorm (L z)
    rw [Real.norm_eq_abs] at hh
    have hb := hh.trans (mul_le_mul (d.first_bound t ht _) (L.le_opNorm z) (norm_nonneg _) C.2)
    dsimp [E]
    rw [abs_div, abs_of_pos hden, hN, zero_add]
    convert (div_le_div_of_nonneg_right hb hden.le) using 1
    ring
  have hiE : Integrable E ((stdGaussian (FiniteStateGaussianInput I)).tilted (fun z => a*A z)) :=
    integrable_finiteStateGaussian_tilt_linear_growth a (Real.sqrt (1-t) • L) (F t) hLip H E hE 0 N hbE
  have he : finiteStateGaussianInputMean a A (finiteStateGaussianShiftedTime d L t H) =
      finiteStateGaussianPriorTimeMean d a L t H-
        finiteStateGaussianVarianceGenerator a (1-t) L (F t) H := by
    change finiteStateGaussianInputMean a A (fun z => D z-E z) = _
    rw [finiteStateGaussianInputMean_sub a A D E hA hD hE hiD hiE]
    rw [show finiteStateGaussianInputMean a A E =
      finiteStateGaussianVarianceGenerator a (1-t) L (F t) H from
        finiteStateGaussianInputMean_raw_gradient_eq_variance a L (F t) (d.spatial_C2 t ht)
          C B (d.first_bound t ht) (d.second_bound t ht) t ht H]
    rfl
  have hh := hasDerivAt_finiteStateGaussianStep_time_raw d a L t ht H
  rw [he] at hh
  exact hh

end FourPapersCommon
