module
public import FourPapersCommon.GenericFiniteStateCascadeParameter
public import Mathlib.Analysis.Calculus.FDeriv.Partial

@[expose] public section

/-! Honest input data and the partial-to-joint chain rule for covariance
interpolation. The terminal data below are discharged for the actual finite
log partition; preservation through the actual cascade is proved separately. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1600000
variable {S I : Type*} [Fintype S] [Fintype I]

def finiteStateGaussianTimeDomain (S : Type*) [Fintype S] : Set (ℝ×FiniteStateField S) :=
  Ioo 0 1 ×ˢ univ

theorem isOpen_finiteStateGaussianTimeDomain : IsOpen (finiteStateGaussianTimeDomain S) :=
  isOpen_Ioo.prod isOpen_univ

structure FiniteStateGaussianTimeData (F : ℝ → FiniteStateField S → ℝ)
    (C B K : ℝ≥0) where
  time : ℝ → FiniteStateField S → ℝ
  cont : ContinuousOn (fun p : ℝ×FiniteStateField S => F p.1 p.2) (finiteStateGaussianTimeDomain S)
  first_cont : ContinuousOn (fun p : ℝ×FiniteStateField S => fderiv ℝ (F p.1) p.2)
    (finiteStateGaussianTimeDomain S)
  second_cont : ContinuousOn (fun p : ℝ×FiniteStateField S => fderiv ℝ (fderiv ℝ (F p.1)) p.2)
    (finiteStateGaussianTimeDomain S)
  spatial_C2 : ∀ t ∈ Ioo 0 1, ContDiff ℝ 2 (F t)
  first_bound : ∀ t ∈ Ioo 0 1, ∀ H, ‖fderiv ℝ (F t) H‖ ≤ C
  second_bound : ∀ t ∈ Ioo 0 1, ∀ H, ‖fderiv ℝ (fderiv ℝ (F t)) H‖ ≤ B
  time_cont : ContinuousOn (fun p : ℝ×FiniteStateField S => time p.1 p.2)
    (finiteStateGaussianTimeDomain S)
  time_hasDeriv : ∀ t ∈ Ioo 0 1, ∀ H, HasDerivAt (fun u => F u H) (time t H) t
  time_bound : ∀ t ∈ Ioo 0 1, ∀ H, |time t H| ≤ K

theorem FiniteStateGaussianTimeData.hasFDerivAt_joint
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K) (t : ℝ) (ht : t ∈ Ioo 0 1)
    (H : FiniteStateField S) :
    HasFDerivAt (fun p : ℝ×FiniteStateField S => F p.1 p.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (d.time t H)).coprod (fderiv ℝ (F t) H)) (t,H) := by
  have hp : (t,H) ∈ finiteStateGaussianTimeDomain S := ⟨ht, mem_univ _⟩
  have hn : ∀ᶠ p : ℝ×FiniteStateField S in 𝓝 (t,H), p.1 ∈ Ioo 0 1 := by
    filter_upwards [isOpen_finiteStateGaussianTimeDomain.mem_nhds hp] with p hp
    exact hp.1
  have h1 : ∀ᶠ p : ℝ×FiniteStateField S in 𝓝 (t,H),
      HasFDerivAt (fun u => F u p.2) (ContinuousLinearMap.toSpanSingleton ℝ (d.time p.1 p.2)) p.1 := by
    filter_upwards [hn] with p hp
    exact (d.time_hasDeriv p.1 hp p.2).hasFDerivAt
  have h2 : ∀ᶠ p : ℝ×FiniteStateField S in 𝓝 (t,H),
      HasFDerivAt (F p.1) (fderiv ℝ (F p.1) p.2) p.2 := by
    filter_upwards [hn] with p hp
    exact ((d.spatial_C2 p.1 hp).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hc1 : ContinuousAt (fun p : ℝ×FiniteStateField S =>
      ContinuousLinearMap.toSpanSingleton ℝ (d.time p.1 p.2)) (t,H) := by
    have hc := d.time_cont.continuousAt (isOpen_finiteStateGaussianTimeDomain.mem_nhds hp)
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp hc
  exact (hasStrictFDerivAt_uncurry_coprod (f := F)
    (f₁ := fun u H => ContinuousLinearMap.toSpanSingleton ℝ (d.time u H))
    (f₂ := fun u H => fderiv ℝ (F u) H) h1 h2 hc1
    (d.first_cont.continuousAt (isOpen_finiteStateGaussianTimeDomain.mem_nhds hp))).hasFDerivAt

theorem FiniteStateGaussianTimeData.hasDerivAt_shifted_input
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) (z : FiniteStateGaussianInput I) :
    HasDerivAt (fun u => F u (H+Real.sqrt (1-u) • L z))
      (d.time t (H+Real.sqrt (1-t) • L z) -
        fderiv ℝ (F t) (H+Real.sqrt (1-t) • L z) (L z)/(2*Real.sqrt (1-t))) t := by
  have hn : 1-t ≠ 0 := ne_of_gt (sub_pos.mpr ht.2)
  have hs := ((Real.hasDerivAt_sqrt hn).comp t
    ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))).smul_const (L z)
  have hh := (hasDerivAt_id t).prodMk (hs.const_add H)
  have hd := (d.hasFDerivAt_joint t ht (H+Real.sqrt (1-t) • L z)).comp_hasDerivAt t hh
  convert hd using 1
  · rfl
  · simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
      map_smul, smul_eq_mul, one_mul, zero_sub]
    ring

def finiteStateGaussianTerminalTimeData [Nonempty S] (V : S → ℝ) :
    FiniteStateGaussianTimeData (fun _ => SpinGlass.AT.gtStateLogPartition V) 1 2 0 where
  time := fun _ _ => 0
  cont := (SpinGlass.AT.contDiff_gtStateLogPartition V).continuous.comp continuous_snd |>.continuousOn
  first_cont := ((SpinGlass.AT.contDiff_gtStateLogPartition V).continuous_fderiv (by simp)).comp
    continuous_snd |>.continuousOn
  second_cont := (((SpinGlass.AT.contDiff_gtStateLogPartition V).fderiv_right
    (m := (1 : ℕ∞ω)) (by simp)).continuous_fderiv (by norm_num)).comp continuous_snd |>.continuousOn
  spatial_C2 := fun _ _ => (SpinGlass.AT.contDiff_gtStateLogPartition V).of_le (by norm_num)
  first_bound := fun _ _ _ => norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianTerminal_lipschitz V)
  second_bound := fun _ _ => norm_second_fderiv_finiteStateGaussianTerminal_le V
  time_cont := continuous_const.continuousOn
  time_hasDeriv := fun t _ H => hasDerivAt_const t (SpinGlass.AT.gtStateLogPartition V H)
  time_bound := fun _ _ _ => by simp

end FourPapersCommon
