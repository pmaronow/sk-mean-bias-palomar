module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeMarkedScore

@[expose] public section

/-! Uniform bounds on the actual recorded posterior response, independent
of depth, all retained Gaussian maps, and the particular retained record. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem cascadePosteriorRecordedMean_bound (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K : FiniteStateField S)
    (h : FiniteHistory (FiniteStateField S) j) :
    ‖cascadePosteriorRecordedMean V a L j i K h‖≤‖K‖ :=
  finiteStateCascadeFirst_abs_le V a ha L (j-i) (historyExtended h i) K

theorem cascadePosteriorRecordedScore_bound (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ) (W : FiniteStateField S)
    (z : FiniteHistory (FiniteStateField S) (N+1)×S) :
    ‖cascadePosteriorRecordedScore V a L N W z‖≤2*‖W‖ := by
  unfold cascadePosteriorRecordedScore
  apply (norm_sub_le _ _).trans
  have hb : ‖∑i,cascadePosteriorStieltjesWeight a N i*
      cascadePosteriorRecordedMean V a L (N+1) (cascadePosteriorScoreTime N i) W z.1‖≤‖W‖ := by
    calc
      _≤∑i,‖cascadePosteriorStieltjesWeight a N i*
        cascadePosteriorRecordedMean V a L (N+1) (cascadePosteriorScoreTime N i) W z.1‖ := norm_sum_le _ _
      _≤∑i,cascadePosteriorStieltjesWeight a N i*‖W‖ := Finset.sum_le_sum fun i _=>by
        rw [norm_mul,Real.norm_of_nonneg (cascadePosteriorStieltjesWeight_nonneg a ha ha1 hdec N i)]
        exact mul_le_mul_of_nonneg_left (cascadePosteriorRecordedMean_bound V a ha L _ _ W z.1)
          (cascadePosteriorStieltjesWeight_nonneg a ha ha1 hdec N i)
      _=‖W‖ := by rw [←Finset.sum_mul,cascadePosteriorStieltjesWeight_sum,one_mul]
  exact (add_le_add (PiLp.norm_apply_le W z.2) hb).trans_eq (by ring)

theorem cascadePosteriorRecordedSecond_bound (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H W K : FiniteStateField S) :
    ‖fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) H W K‖≤‖W‖*‖K‖ := by
  let B:=fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) H
  have hb : ‖B‖≤1 := by
    rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
    exact norm_finiteStateCascade_secondJet_le_one V a ha ha1 hdec L j H
  exact ((B W).le_opNorm K).trans
    ((mul_le_mul_of_nonneg_right ((B.le_opNorm W).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg W)))
        (norm_nonneg K)))

theorem cascadePosteriorRecordedSquareResponse_bound (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N i : ℕ) (K W : FiniteStateField S)
    (z : FiniteHistory (FiniteStateField S) (N+1)×S) :
    ‖cascadePosteriorRecordedSquareResponse V a L N i K W z‖≤4*‖K‖^2*‖W‖ := by
  have hm:=cascadePosteriorRecordedMean_bound V a ha L (N+1) i K z.1
  have hh:=cascadePosteriorRecordedSecond_bound V a ha ha1 hdec L (N+1-i) (historyExtended z.1 i) W K
  have hd:=cascadePosteriorRecordedScore_bound V a ha ha1 hdec L N W z
  unfold cascadePosteriorRecordedSquareResponse
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_pow,Real.norm_ofNat]
  have h1:=mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤2)) hh (norm_nonneg _) (by positivity : (0:ℝ)≤2*‖K‖)
  have h2:=mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hm 2) hd (norm_nonneg _) (by positivity)
  exact (add_le_add h1 h2).trans_eq (by ring)

end QuantitativeFollowup
