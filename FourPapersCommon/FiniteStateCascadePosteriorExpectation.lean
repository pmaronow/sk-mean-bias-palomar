module
public import FourPapersCommon.FiniteStateCascadePosteriorLogDensity
public import FourPapersCommon.FiniteStateCascadeRecurrence
public import FourPapersCommon.FiniteStateCascadeHessianTelescoping
public import FourPapersCommon.HistoryBackwardFiniteEndpoint

@[expose] public section

/-! The actual normalized remaining posterior differentiates the literal
finite cascade, with no assumed conditional-spin or expectation identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT QuantitativePaper
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1200000

theorem integral_cascadePosteriorLaw_coordinate (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H K : FiniteStateField S) :
    (∫z,K z.2 ∂cascadePosteriorLaw V a L j H)=
      fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H K := by
  haveI := cascadePosteriorLaw_probability V a ha L j H
  haveI := cascadePosteriorHistoryLaw_probability V a ha L j H
  have hi : Integrable (fun z : FiniteHistory (FiniteStateField S) j×S=>K z.2)
      (cascadePosteriorLaw V a L j H) :=
    source_bounded_integrable _ _ ((measurable_of_finite _).comp measurable_snd) ‖K‖
      (fun z=>by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le K z.2))
  rw [cascadePosteriorLaw,Measure.integral_compProd hi]
  have hf0 : (fun h : FiniteHistory (FiniteStateField S) j=>
      ∫σ,K σ ∂cascadePosteriorTerminalKernel V j h)=
      fun h=>fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j-j)) (h (Fin.last j)) K := by
    funext h
    rw [cascadePosteriorTerminalKernel,Kernel.comap_apply]
    simp only [Nat.sub_self,finiteStateGaussianTerminalCascade,finiteStateGaussianCascade]
    rw [integral_finiteStateGibbsKernel,fderiv_gtStateLogPartition_apply]
  rw [hf0]
  change (∫h,(fun i Q=>fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j-i)) Q K)
    j (h (Fin.last j)) ∂finiteHistoryLaw (Measure.dirac H) (cascadePosteriorKernel V a L j) j)=_
  rw [integral_history_backward_at_initial_upto (Measure.dirac H) (cascadePosteriorKernel V a L j)
    (fun i=>cascadePosteriorKernel_markov V a ha L j i) j
    (fun i Q=>fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j-i)) Q K)
    (fun i _=>((contDiff_one_finiteStateGaussianTerminalCascade V a ha L (j-i)).continuous_fderiv
      (by norm_num)).clm_apply continuous_const |>.measurable)
    ‖K‖ (fun i _ Q=>finiteStateCascadeFirst_abs_le V a ha L (j-i) Q K)
    (fun i hi Q=>by
      have hd : j-i=(j-1-i)+1 := by omega
      have he : j-(i+1)=j-1-i := by omega
      rw [hd,fderiv_finiteStateGaussianTerminalCascade_succ_integral V a ha L]
      rw [he]
      rfl),integral_dirac]
  simp

theorem integral_cascadePosterior_exp_coordinate (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H K : FiniteStateField S) :
    (∫z,Real.exp (cascadePosteriorLogDensity V a L j H z)*K z.2
      ∂cascadePosteriorGaussianBase S (Fin n) j)=
      fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H K := by
  have hh := integral_cascadePosteriorLaw_coordinate V a ha L j H K
  rw [←cascadePosteriorGaussianLaw_map V a ha L j H,
    integral_map (f:=fun z : FiniteHistory (FiniteStateField S) j×S=>K z.2)
      (measurable_cascadePosteriorCoordinateMap L j H).aemeasurable
      ((measurable_of_finite _).comp measurable_snd).aestronglyMeasurable,
    cascadePosteriorGaussianLaw_eq_exp_density V a ha L j H,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_cascadePosteriorLogDensity V a ha L j H).exp.ennreal_ofReal)
      (Eventually.of_forall fun z=>ENNReal.ofReal_lt_top)] at hh
  simpa only [cascadePosteriorCoordinateMap,ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul] using hh

end FourPapersCommon
