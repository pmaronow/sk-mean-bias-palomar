module
public import FourPapersCommon.GenericFiniteStateCascadeFamilyContinuity
public import FourPapersCommon.FiniteStateGaussianCoordinateMeans

@[expose] public section

/-! Genuine differentiation of a Gaussian step with a time-dependent preceding
potential. The local envelopes come from its already-proved spatial bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 800000
variable {S I : Type*} [Fintype S] [Fintype I]

private theorem eventually_norm_bound {A V : Type*} [TopologicalSpace A]
    [NormedAddCommGroup V] {f : A → V} {p : A} (hf : ContinuousAt f p) :
    ∀ᶠ q in 𝓝 p, ‖f q‖ ≤ ‖f p‖+1 :=
  (hf.norm.tendsto.eventually (eventually_lt_nhds (by linarith))).mono fun _ h => h.le

theorem finiteStateGaussianTimeData_local_growth
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    ∀ᶠ u in 𝓝 t, u ∈ Ioo 0 1 ∧ ∀ z : FiniteStateGaussianInput I,
      |F u (H+Real.sqrt (1-u) • L z)| ≤
        |F t H|+1+(C*(|Real.sqrt (1-t)|+1)*‖L‖)*‖z‖ := by
  have htime : ∀ᶠ u in 𝓝 t, u ∈ Ioo 0 1 := isOpen_Ioo.mem_nhds ht
  have hc : ContinuousAt (fun u => F u H) t := (d.time_hasDeriv t ht H).continuousAt
  have hs : ContinuousAt (fun u : ℝ => Real.sqrt (1-u)) t := by fun_prop
  filter_upwards [htime, eventually_norm_bound hc, eventually_norm_bound hs] with u hu huf hus
  refine ⟨hu, fun z => ?_⟩
  simp only [Real.norm_eq_abs] at huf hus
  have hLip : LipschitzWith C (F u) := lipschitzWith_of_nnnorm_fderiv_le
    ((d.spatial_C2 u hu).differentiable (by norm_num))
      (fun y => NNReal.coe_le_coe.mp (d.first_bound u hu y))
  have hh := hLip.norm_sub_le (H+Real.sqrt (1-u) • L z) H
  simp only [Real.norm_eq_abs, add_sub_cancel_left, norm_smul] at hh
  have hnorm := mul_le_mul hus (L.le_opNorm z) (norm_nonneg _) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hnorm C.2
  calc
    _ = |(F u (H+Real.sqrt (1-u) • L z)-F u H)+F u H| := by congr 1; ring
    _ ≤ |F u (H+Real.sqrt (1-u) • L z)-F u H|+|F u H| := abs_add_le _ _
    _ ≤ C*(|Real.sqrt (1-u)| *‖L z‖)+(|F t H|+1) := add_le_add hh huf
    _ ≤ C*((|Real.sqrt (1-t)|+1)*(‖L‖*‖z‖))+(|F t H|+1) := add_le_add hmul le_rfl
    _ = _ := by ring

def finiteStateGaussianShiftedTime
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (t : ℝ) (H : FiniteStateField S) (z : FiniteStateGaussianInput I) : ℝ :=
  d.time t (H+Real.sqrt (1-t) • L z) -
    fderiv ℝ (F t) (H+Real.sqrt (1-t) • L z) (L z)/(2*Real.sqrt (1-t))

theorem hasDerivAt_finiteStateGaussianStep_time_raw
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    HasDerivAt (fun u => finiteStateGaussianStep a (Real.sqrt (1-u) • L) (F u) H)
      (finiteStateGaussianInputMean a
        (fun z => F t (H+Real.sqrt (1-t) • L z))
        (finiteStateGaussianShiftedTime d L t H)) t := by
  have hlocal := finiteStateGaussianTimeData_local_growth d L t ht H
  have hs : ContinuousAt (fun u : ℝ => (2*Real.sqrt (1-u))⁻¹) t := by
    apply ContinuousAt.inv₀
    · fun_prop
    · exact mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr ht.2)))
  have hi := eventually_norm_bound hs
  let J : Set ℝ := {u | u ∈ Ioo 0 1 ∧
    (∀ z : FiniteStateGaussianInput I, |F u (H+Real.sqrt (1-u) • L z)| ≤
      |F t H|+1+(C*(|Real.sqrt (1-t)|+1)*‖L‖)*‖z‖) ∧
    |(2*Real.sqrt (1-u))⁻¹| ≤ |(2*Real.sqrt (1-t))⁻¹|+1}
  have hJ : J ∈ 𝓝 t := by
    filter_upwards [hlocal, hi] with u hu hiu
    exact ⟨hu.1,hu.2,by simpa only [Real.norm_eq_abs] using hiu⟩
  let c : ℝ≥0 := Real.toNNReal (C*(|Real.sqrt (1-t)|+1)*‖L‖)
  let c' : ℝ≥0 := Real.toNNReal (C*‖L‖*(|(2*Real.sqrt (1-t))⁻¹|+1))
  have hc : (c : ℝ) = C*(|Real.sqrt (1-t)|+1)*‖L‖ := Real.coe_toNNReal _ (by positivity)
  have hc' : (c' : ℝ) = C*‖L‖*(|(2*Real.sqrt (1-t))⁻¹|+1) := Real.coe_toNNReal _ (by positivity)
  have hF (u : ℝ) (hu : u ∈ J) : Measurable (fun z : FiniteStateGaussianInput I =>
      F u (H+Real.sqrt (1-u) • L z)) := by
    exact ((d.spatial_C2 u hu.1).continuous.comp
      (continuous_const.add (L.continuous.const_smul (Real.sqrt (1-u))))).measurable
  have hD (u : ℝ) (hu : u ∈ J) : Measurable (finiteStateGaussianShiftedTime d L u H) := by
    have hcT : Continuous (d.time u) := continuousOn_univ.mp
      (d.time_cont.comp (continuous_const.prodMk continuous_id).continuousOn (fun y _ => ⟨hu.1,mem_univ y⟩))
    have hmap : Continuous (fun z : FiniteStateGaussianInput I => H+Real.sqrt (1-u) • L z) :=
      continuous_const.add (L.continuous.const_smul (Real.sqrt (1-u)))
    have hcD := (d.spatial_C2 u hu.1).continuous_fderiv (by norm_num)
    exact ((hcT.comp hmap).sub (((hcD.comp hmap).clm_apply L.continuous).div_const _)).measurable
  have hb' (u : ℝ) (hu : u ∈ J) (z : FiniteStateGaussianInput I) :
      |finiteStateGaussianShiftedTime d L u H z| ≤ (K : ℝ)+c'*‖z‖ := by
    have hd := (fderiv ℝ (F u) (H+Real.sqrt (1-u) • L z)).le_opNorm (L z)
    rw [Real.norm_eq_abs] at hd
    have hb := hd.trans (mul_le_mul (d.first_bound u hu.1 _) (L.le_opNorm z) (norm_nonneg _) C.2)
    have hm := mul_le_mul hb hu.2.2 (abs_nonneg _) (by positivity)
    calc
      _ ≤ |d.time u (H+Real.sqrt (1-u) • L z)|+
        |fderiv ℝ (F u) (H+Real.sqrt (1-u) • L z) (L z)/(2*Real.sqrt (1-u))| := abs_sub _ _
      _ ≤ K+c'*‖z‖ := by
        apply add_le_add (d.time_bound u hu.1 _)
        rw [div_eq_mul_inv, abs_mul, hc']
        convert hm using 1
        ring
  have hh := hasDerivAt_finiteStateGaussianInputStep_parameter a
    (fun u z => F u (H+Real.sqrt (1-u) • L z))
    (fun u => finiteStateGaussianShiftedTime d L u H) t J hJ (|F t H|+1) K c c'
    hF hD (fun u hu z => d.hasDerivAt_shifted_input L u hu.1 H z)
    (fun u hu z => by rw [hc]; exact hu.2.1 z) hb'
  simpa only [finiteStateGaussianStep, smul_apply] using hh

end FourPapersCommon
