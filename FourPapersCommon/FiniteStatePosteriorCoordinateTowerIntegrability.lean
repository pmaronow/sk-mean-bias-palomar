module
public import FourPapersCommon.FiniteStatePosteriorCoordinateTowerBounded
public import FourPapersCommon.FiniteStatePosteriorCoordinateTowerMoment

@[expose] public section

/-! Honest integrability of recorded Gaussian coordinates under the whole
posterior, obtained from its bounded tower and a Gaussian envelope. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal Topology
namespace FourPapersCommon
open SpinGlass.AT OverlapPaper
set_option maxHeartbeats 1200000

 theorem integrable_of_uniform_truncated_integrals {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω→ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀n : ℕ,(∫x,min |f x| (n:ℝ) ∂P)≤C) : Integrable f P := by
  let F := fun (n : ℕ) (x : Ω)=>ENNReal.ofReal (min |f x| (n:ℝ))
  have hFm (n : ℕ) : Measurable (F n) := (hf.abs.min measurable_const).ennreal_ofReal
  have hlim (x : Ω) : Tendsto (fun n=>F n x) atTop (𝓝 (ENNReal.ofReal |f x|)) := by
    obtain ⟨N,hN⟩:=exists_nat_gt |f x|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    dsimp only [F]
    rw [min_eq_left (hN.le.trans (by exact_mod_cast hn))]
  have hb (n : ℕ) : (∫⁻x,F n x ∂P)≤ENNReal.ofReal C := by
    have hi : Integrable (fun x=>min |f x| (n:ℝ)) P :=
      source_bounded_integrable _ _ (hf.abs.min measurable_const) (n:ℝ) (fun x=>by
        rw [abs_of_nonneg (le_min (abs_nonneg _) (Nat.cast_nonneg _))]
        exact min_le_right _ _)
    rw [←ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun x=>le_min (abs_nonneg _) (Nat.cast_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hC n)
  have hfatou : (∫⁻x,ENNReal.ofReal |f x| ∂P)≤ENNReal.ofReal C := by
    calc
      _ = ∫⁻x,liminf (fun n=>F n x) atTop ∂P :=
        lintegral_congr fun x=>(hlim x).liminf_eq.symm
      _ ≤ liminf (fun n=>∫⁻x,F n x ∂P) atTop := lintegral_liminf_le' (fun n=>(hFm n).aemeasurable)
      _ ≤ ENNReal.ofReal C := liminf_le_of_frequently_le' (Frequently.of_forall hb)
  apply (integrable_norm_iff hf.aestronglyMeasurable).mp
  simpa only [Real.norm_eq_abs] using
    (lintegral_ofReal_ne_top_iff_integrable hf.abs.aestronglyMeasurable
      (.of_forall fun x=>abs_nonneg (f x))).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfatou)

variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

def posteriorCoordinateMomentBound (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (d : ℕ) : ℝ :=
  (∫z,Real.exp ((|a d| *‖L d‖+1)*‖z‖) ∂stdGaussian (FiniteStateGaussianInput I))/
    posteriorCoordinateGaussianLower I (|a d| *‖L d‖)

 theorem posteriorCoordinateMomentBound_nonneg (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (d : ℕ) :
    0≤posteriorCoordinateMomentBound a L d := by
  apply div_nonneg (integral_nonneg fun _=>(Real.exp_pos _).le)
    (posteriorCoordinateGaussianLower_pos _).le

 theorem integral_coordinateSpin_truncated_abs_le (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (d : ℕ)
    (H : FiniteStateField S) (i : Fin (Fintype.card I)) (n : ℕ) :
    (∫z,min |(finiteStateGaussianBasis I).repr z.1 i| (n:ℝ)
      ∂finiteStateGaussianCoordinateSpinLaw V a L d H)≤posteriorCoordinateMomentBound a L d := by
  let P := (stdGaussian (FiniteStateGaussianInput I)).tilted
    (fun z=>a d*finiteStateGaussianTerminalCascade V a L d (H+L d z))
  haveI:=finiteStateGaussianCoordinateSpinKernel_markov V a ha L d H
  haveI : IsProbabilityMeasure P:=isProbabilityMeasure_tilted (integrable_exp_finiteStateGaussian_lipschitz
    _ (finiteStateGaussianTerminalCascade_lipschitz V a ha L d) (L d) H (a d))
  have hi : Integrable (fun z : FiniteStateGaussianInput I×S=>
      min |(finiteStateGaussianBasis I).repr z.1 i| (n:ℝ))
      (finiteStateGaussianCoordinateSpinLaw V a L d H) := by
    haveI:=finiteStateGaussianCoordinateSpinLaw_probability V a ha L d H
    exact source_bounded_integrable _ _
      ((((continuous_finiteStateGaussianInput_coordinate i).measurable.comp measurable_fst).abs).min measurable_const)
      (n:ℝ) (fun z=>by rw [abs_of_nonneg (le_min (abs_nonneg _) (Nat.cast_nonneg _))];exact min_le_right _ _)
  rw [finiteStateGaussianCoordinateSpinLaw,Measure.integral_compProd hi]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  rw [integral_tilted]
  let c := |a d| *‖L d‖
  have hp := posteriorCoordinateGaussianLower_pos (I:=I) c
  have henv : Integrable (fun z : FiniteStateGaussianInput I=>
      Real.exp ((c+1)*‖z‖)/posteriorCoordinateGaussianLower I c)
      (stdGaussian (FiniteStateGaussianInput I)) :=
    (integrable_exp_mul_norm_gaussian _ (c+1)).div_const _
  have hleft : Integrable (fun z : FiniteStateGaussianInput I=>
      (Real.exp (a d*finiteStateGaussianTerminalCascade V a L d (H+L d z))/
        ∫w,Real.exp (a d*finiteStateGaussianTerminalCascade V a L d (H+L d w)) ∂stdGaussian (FiniteStateGaussianInput I))*
      min |(finiteStateGaussianBasis I).repr z i| (n:ℝ))
      (stdGaussian (FiniteStateGaussianInput I)) := by
    have hm : Measurable (fun z : FiniteStateGaussianInput I=>
      (Real.exp (a d*finiteStateGaussianTerminalCascade V a L d (H+L d z))/
        ∫w,Real.exp (a d*finiteStateGaussianTerminalCascade V a L d (H+L d w)) ∂stdGaussian (FiniteStateGaussianInput I))*
      min |(finiteStateGaussianBasis I).repr z i| (n:ℝ)) :=
      ((((contDiff_one_finiteStateGaussianTerminalCascade V a ha L d).continuous.measurable.comp
      (show Measurable (fun z : FiniteStateGaussianInput I=>H+L d z) by fun_prop)).const_mul (a d)).exp.div_const _).mul
        ((continuous_finiteStateGaussianInput_coordinate i).measurable.abs.min measurable_const)
    apply henv.mono' hm.aestronglyMeasurable (.of_forall fun z=>?_) 
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    apply (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans
    simpa only [NNReal.coe_one,mul_one,c] using posteriorCoordinateGaussian_coordinate_envelope
      (a d) (L d) _ (finiteStateGaussianTerminalCascade_lipschitz V a ha L d) H z i
  have hh := integral_mono hleft henv (fun z=>by
    apply (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans
    simpa only [NNReal.coe_one,mul_one,c] using posteriorCoordinateGaussian_coordinate_envelope
      (a d) (L d) _ (finiteStateGaussianTerminalCascade_lipschitz V a ha L d) H z i)
  simpa only [smul_eq_mul,posteriorCoordinateMomentBound,c,integral_div] using hh

/-- Every literal raw Gaussian coordinate is integrable under the actual
all-input cascade posterior, even if its covariance direction is zero. -/
theorem integrable_cascadePosteriorGaussianLaw_input_coordinate (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (N : ℕ) (H : FiniteStateField S) (r : Fin N) (i : Fin (Fintype.card I)) :
    Integrable (fun z : (Fin N→FiniteStateGaussianInput I)×S=>(finiteStateGaussianBasis I).repr (z.1 r) i)
      (cascadePosteriorGaussianLaw V a L N H) := by
  haveI:=cascadePosteriorGaussianLaw_probability V a ha L N H
  haveI:=posteriorCoordinateHistoryLaw_probability V a ha L N H r.val
  apply integrable_of_uniform_truncated_integrals _ _
    ((continuous_finiteStateGaussianInput_coordinate i).measurable.comp
      ((measurable_pi_apply r).comp measurable_fst)) (posteriorCoordinateMomentBound a L (N-1-r.val))
  intro n
  let K : FiniteStateField S:=WithLp.toLp 2 (fun _=>1)
  have hh:=cascadePosteriorGaussianLaw_coordinate_feature_tower_bounded V a ha L N H K r
    (fun z=>min |(finiteStateGaussianBasis I).repr z i| (n:ℝ))
    ((continuous_finiteStateGaussianInput_coordinate i).measurable.abs.min measurable_const)
    (n:ℝ) (fun z=>by rw [abs_of_nonneg (le_min (abs_nonneg _) (Nat.cast_nonneg _))];exact min_le_right _ _)
  have hK : ∀σ,K σ=1 := fun _=>rfl
  simp only [hK,mul_one] at hh
  simp only [Function.comp_def]
  rw [hh]
  apply (le_abs_self _).trans
  have hn := norm_integral_le_of_norm_le_const (μ:=posteriorCoordinateHistoryLaw V a L N H r.val)
    (f:=fun h=>∫z,min |(finiteStateGaussianBasis I).repr z.1 i| (n:ℝ)
      ∂finiteStateGaussianCoordinateSpinLaw V a L (N-1-r.val) (h (Fin.last r.val)).1)
    (.of_forall fun h=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun z=>le_min (abs_nonneg _) (Nat.cast_nonneg _))]
      exact integral_coordinateSpin_truncated_abs_le V a ha L _ _ i n)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hn

end FourPapersCommon
