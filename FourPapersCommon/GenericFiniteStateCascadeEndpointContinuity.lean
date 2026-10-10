module
public import FourPapersCommon.GenericFiniteStateCascadeInterpolation

@[expose] public section

/-! Genuine continuity of the finite Gaussian interpolation at zero-variance
endpoints. No derivative at a square-root endpoint is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 800000
variable {S I : Type*} [Fintype S] [Fintype I]

private theorem eventually_norm_bound {P V : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] {f : P → V} {p : P} (hf : ContinuousAt f p) :
    ∀ᶠ q in 𝓝 p, ‖f q‖ ≤ ‖f p‖+1 :=
  (hf.norm.tendsto.eventually (eventually_lt_nhds (by linarith))).mono fun _ h => h.le

theorem continuous_finiteStateGaussianStep_family
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    (a : ℝ) (F : P → FiniteStateField S → ℝ)
    (hF : Continuous (fun p : P×FiniteStateField S => F p.1 p.2))
    (C : ℝ≥0) (hLip : ∀ p, LipschitzWith C (F p))
    (L : P → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (hL : Continuous L)
    (H : P → FiniteStateField S) (hH : Continuous H) :
    Continuous (fun p => finiteStateGaussianStep a (L p) (F p) (H p)) := by
  rw [continuous_iff_continuousAt]
  intro p
  let φ := fun q z => F q (H q+L q z)
  have hφ (z : FiniteStateGaussianInput I) : Continuous (fun q => φ q z) :=
    hF.comp (continuous_id.prodMk (hH.add (hL.clm_apply continuous_const)))
  have hφq (q : P) : Continuous (φ q) :=
    (hLip q).continuous.comp (continuous_const.add (L q).continuous)
  let M : ℝ := |F p (H p)|+1+C
  let D : ℝ := C*(‖L p‖+1)
  have hloc : ∀ᶠ q in 𝓝 p, ∀ z : FiniteStateGaussianInput I, |φ q z| ≤ M+D*‖z‖ := by
    have hFc : ContinuousAt (fun q => F q (H p)) p :=
      (hF.comp (continuous_id.prodMk continuous_const)).continuousAt
    have hHc : ContinuousAt (fun q => H q-H p) p := (hH.sub continuous_const).continuousAt
    filter_upwards [eventually_norm_bound hFc, eventually_norm_bound hHc,
      eventually_norm_bound hL.continuousAt] with q hqF hqH hqL z
    simp only [Real.norm_eq_abs] at hqF
    simp only [sub_self,norm_zero,zero_add] at hqH
    have hd := (hLip q).norm_sub_le (H q+L q z) (H p)
    rw [Real.norm_eq_abs] at hd
    have hn : ‖H q+L q z-H p‖ ≤ 1+(‖L p‖+1)*‖z‖ := by
      rw [show H q+L q z-H p=(H q-H p)+L q z by abel]
      exact (norm_add_le _ _).trans (add_le_add hqH ((L q).le_opNorm z |>.trans
        (mul_le_mul_of_nonneg_right hqL (norm_nonneg z))))
    have hh := mul_le_mul_of_nonneg_left hn C.2
    have htri := abs_add_le (φ q z-F q (H p)) (F q (H p))
    rw [sub_add_cancel] at htri
    dsimp [φ] at htri ⊢
    calc
      _ ≤ |F q (H q+L q z)-F q (H p)|+|F q (H p)| := htri
      _ ≤ C*(1+(‖L p‖+1)*‖z‖)+(|F p (H p)|+1) := add_le_add (hd.trans hh) hqF
      _ = _ := by dsimp [M,D]; ring
  have hi : ContinuousAt (fun q => ∫ z, φ q z ∂stdGaussian (FiniteStateGaussianInput I)) p := by
    apply continuousAt_of_dominated (bound := fun z => M+D*‖z‖)
    · exact .of_forall fun q => (hφq q).aestronglyMeasurable
    · exact hloc.mono fun q hq => .of_forall fun z => by simpa only [Real.norm_eq_abs] using hq z
    · exact (integrable_const M).add
        ((IsGaussian.integrable_id (μ := stdGaussian (FiniteStateGaussianInput I))).norm.const_mul D)
    · exact .of_forall fun z => (hφ z).continuousAt
  have hei : ContinuousAt (fun q => ∫ z, Real.exp (a*φ q z) ∂stdGaussian (FiniteStateGaussianInput I)) p := by
    apply continuousAt_of_dominated
      (bound := fun z => Real.exp (|a| *M)*Real.exp ((|a| *D)*‖z‖))
    · exact .of_forall fun q => (Real.continuous_exp.comp ((hφq q).const_mul a)).aestronglyMeasurable
    · filter_upwards [hloc] with q hq
      exact .of_forall fun z => by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
        apply Real.exp_le_exp.2
        have ha := le_abs_self (a*φ q z)
        rw [abs_mul] at ha
        have hh := mul_le_mul_of_nonneg_left (hq z) (abs_nonneg a)
        linarith
    · exact (integrable_exp_mul_norm_gaussian (stdGaussian (FiniteStateGaussianInput I)) (|a| *D)).const_mul _
    · exact .of_forall fun z => (Real.continuous_exp.comp ((hφ z).const_mul a)).continuousAt
  by_cases ha : a=0
  · simpa only [finiteStateGaussianStep,OverlapPaper.sourceLogAverage,ha,ite_true,φ] using hi
  · have hp : (∫ z, Real.exp (a*φ p z) ∂stdGaussian (FiniteStateGaussianInput I)) ≠ 0 :=
      (integral_exp_pos (integrable_exp_finiteStateGaussian_lipschitz (F p) (hLip p) (L p) (H p) a)).ne'
    simpa only [finiteStateGaussianStep,OverlapPaper.sourceLogAverage,ha,ite_false,φ] using
      (hei.log hp).div_const a

theorem continuous_finiteStateGaussianInterpolatedTerminalCascade [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    Continuous (fun p : ℝ×FiniteStateField S => finiteStateGaussianInterpolatedTerminalCascade V a A j p.1 p.2) := by
  induction j with
  | zero => exact (SpinGlass.AT.contDiff_gtStateLogPartition V).continuous.comp continuous_snd
  | succ j ih =>
    change Continuous (fun p : ℝ×FiniteStateField S => finiteStateGaussianStep (a j)
      (Real.sqrt (1-p.1) • A j) (finiteStateGaussianInterpolatedTerminalCascade V a A j p.1) p.2)
    exact continuous_finiteStateGaussianStep_family (a j)
      (fun p : ℝ×FiniteStateField S => fun H => finiteStateGaussianInterpolatedTerminalCascade V a A j p.1 H)
      (ih.comp ((continuous_fst.fst).prodMk continuous_snd)) 1
      (fun _ => finiteStateGaussianTerminalCascade_lipschitz V a ha _ j)
      (fun p : ℝ×FiniteStateField S => Real.sqrt (1-p.1) • A j) (by fun_prop)
      (fun p : ℝ×FiniteStateField S => p.2) continuous_snd

theorem continuous_finiteStateGaussianTerminalCascade_outer_time [Nonempty S]
    {I' : Type*} [Fintype I']
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (M : FiniteStateGaussianInput I' →L[ℝ] FiniteStateField S)
    (j : ℕ) (H : FiniteStateField S) :
    Continuous (fun t => finiteStateGaussianStep 0 (Real.sqrt t • M)
      (finiteStateGaussianInterpolatedTerminalCascade V a A j t) H) :=
  continuous_finiteStateGaussianStep_family 0 (finiteStateGaussianInterpolatedTerminalCascade V a A j)
    (continuous_finiteStateGaussianInterpolatedTerminalCascade V a ha A j) 1
    (fun _ => finiteStateGaussianTerminalCascade_lipschitz V a ha _ j)
    (fun t => Real.sqrt t • M) (by fun_prop) (fun _ => H) continuous_const

end FourPapersCommon
