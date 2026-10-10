module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeFinite

@[expose] public section

/-! The actual retained magnetization square under the normalized remaining
Gaussian posterior. All observable and differential bounds are uniform in
the number and the covariances of the remaining steps. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def cascadePosteriorRetainedMean (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K H : FiniteStateField S)
    (z : (Fin j→Field n)×S) : ℝ :=
  fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j-i))
    (historyExtended (cascadePosteriorHistory L j H z.1) i) K

def cascadePosteriorRetainedSquare (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K H : FiniteStateField S)
    (z : (Fin j→Field n)×S) : ℝ :=
  (cascadePosteriorRetainedMean V a L j i K H z)^2

theorem contDiff_cascadePosteriorRetainedMean (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K : FiniteStateField S) :
    ContDiff ℝ ∞ (fun z : (Fin j→Field n)×FiniteStateField S=>
      cascadePosteriorRetainedMean V a L j i K z.2 (z.1,Classical.choice inferInstance)) := by
  have hd := (contDiff_finiteStateGaussianTerminalCascade V a ha L (j-i)).fderiv_right
    (m:=∞) (by simp)
  have hp := (contDiff_apply ℝ (FiniteStateField S) (Fin.ofNat (j+1) i)).comp
    ((contDiff_cascadePosteriorHistory L j).comp (contDiff_snd.prodMk contDiff_fst))
  exact (hd.comp hp).clm_apply contDiff_const

theorem cascadePosteriorRetainedMean_bound (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K H : FiniteStateField S)
    (z : (Fin j→Field n)×S) : |cascadePosteriorRetainedMean V a L j i K H z|≤‖K‖ := by
  have hd:=norm_finiteStateCascade_firstJet_le_one V a ha L (j-i)
    (historyExtended (cascadePosteriorHistory L j H z.1) i)
  rw [norm_iteratedFDeriv_one] at hd
  exact ((fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j-i))
    (historyExtended (cascadePosteriorHistory L j H z.1) i)).le_opNorm K).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hd (norm_nonneg K))

theorem finiteStateCascade_differential_lipschitz (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) :
    LipschitzWith 1 (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) := by
  have hs:=(contDiff_finiteStateGaussianTerminalCascade V a ha L j).fderiv_right (m:=∞) (by simp)
  apply lipschitzWith_of_nnnorm_fderiv_le (hs.differentiable (by simp))
  intro H
  apply NNReal.coe_le_coe.mp
  change ‖fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) H‖≤(1:ℝ)
  rw [←norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact norm_finiteStateCascade_secondJet_le_one V a ha ha1 hdec L j H

theorem cascadePosteriorRetainedMean_lipschitz (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K : FiniteStateField S)
    (z : (Fin j→Field n)×S) :
    LipschitzWith ‖K‖₊ (fun H=>cascadePosteriorRetainedMean V a L j i K H z) := by
  apply LipschitzWith.of_dist_le_mul
  intro H Q
  unfold cascadePosteriorRetainedMean
  dsimp only [historyExtended]
  rw [cascadePosteriorHistory_eq_initial_add L j H z.1,
    cascadePosteriorHistory_eq_initial_add L j Q z.1]
  rw [Real.dist_eq,←ContinuousLinearMap.sub_apply]
  have hh := (finiteStateCascade_differential_lipschitz V a ha ha1 hdec L (j-i)).norm_sub_le
    (H+cascadePosteriorHistory L j 0 z.1 (Fin.ofNat (j+1) i))
    (Q+cascadePosteriorHistory L j 0 z.1 (Fin.ofNat (j+1) i))
  simp only [NNReal.coe_one,one_mul,add_sub_add_right_eq_sub] at hh
  exact ((fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j-i))
    (H+cascadePosteriorHistory L j 0 z.1 (Fin.ofNat (j+1) i))-
    fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j-i))
    (Q+cascadePosteriorHistory L j 0 z.1 (Fin.ofNat (j+1) i))).le_opNorm K).trans
      (by simpa only [coe_nnnorm,dist_eq_norm,mul_comm] using mul_le_mul_of_nonneg_right hh (norm_nonneg K))

theorem cascadePosteriorRetainedSquare_differential_bound (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K H : FiniteStateField S)
    (z : (Fin j→Field n)×S) :
    ‖fderiv ℝ (fun Q=>cascadePosteriorRetainedSquare V a L j i K Q z) H‖≤2*‖K‖^2 := by
  let f:=fun Q=>cascadePosteriorRetainedMean V a L j i K Q z
  have hd : DifferentiableAt ℝ f H := by
    have hs:=contDiff_cascadePosteriorRetainedMean V a ha L j i K
    have hF : ContDiff ℝ ∞ f := hs.comp (contDiff_const.prodMk contDiff_id)
    exact hF.differentiable (by simp) H
  have hb : ‖fderiv ℝ f H‖≤‖K‖:=
    norm_fderiv_le_of_lipschitz ℝ (cascadePosteriorRetainedMean_lipschitz V a ha ha1 hdec L j i K z)
  change ‖fderiv ℝ (f^2) H‖≤_
  rw [fderiv_pow 2 hd, norm_smul,Real.norm_eq_abs]
  norm_num only [Nat.cast_ofNat, pow_one,nsmul_eq_mul]
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hm:=cascadePosteriorRetainedMean_bound V a ha L j i K H z
  calc
    _ ≤ (2*‖K‖)*‖K‖ := mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num)) hb
      (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem hasFDerivAt_cascadePosterior_retained_square (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K H : FiniteStateField S) :
    HasFDerivAt (fun Q=>∫z,cascadePosteriorRetainedSquare V a L j i K Q z
        ∂cascadePosteriorGaussianLaw V a L j Q)
      (∫z,fderiv ℝ (fun Q=>cascadePosteriorRetainedSquare V a L j i K Q z) H+
        cascadePosteriorRetainedSquare V a L j i K H z •
          fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L j Q z) H
        ∂cascadePosteriorGaussianLaw V a L j H) H := by
  let F:=cascadePosteriorRetainedSquare V a L j i K
  have hs : ContDiff ℝ ∞ (fun z : (Fin j→Field n)×FiniteStateField S=>
      F z.2 (z.1,Classical.choice inferInstance)) :=
    (contDiff_cascadePosteriorRetainedMean V a ha L j i K).pow 2
  have hFm (Q : FiniteStateField S) : Measurable (F Q) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact (hs.continuous.comp (continuous_id.prodMk continuous_const)).measurable
  have hFDm (Q : FiniteStateField S) : Measurable (fun z=>fderiv ℝ (fun H=>F H z) Q) := by
    apply measurable_from_prod_countable_left
    intro σ
    have hd : Continuous (fun z : (Fin j→Field n)×FiniteStateField S=>
        fderiv ℝ (fun H=>F H (z.1,Classical.choice inferInstance)) z.2) :=
      continuous_iff_continuousAt.mpr fun z=>
        (contDiffAt_partial_fderiv _ z hs.contDiffAt).continuousAt
    exact (hd.comp (continuous_id.prodMk (continuous_const (y:=Q)))).measurable
  have hFD (z : (Fin j→Field n)×S) (Q : FiniteStateField S) :
      DifferentiableAt ℝ (fun H=>F H z) Q :=
    (hs.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) Q
  have hFb (Q : FiniteStateField S) (z : (Fin j→Field n)×S) : |F Q z|≤‖K‖^2 := by
    simpa only [F,cascadePosteriorRetainedSquare,abs_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (cascadePosteriorRetainedMean_bound V a ha L j i K Q z) 2
  exact hasFDerivAt_cascadePosteriorGaussianLaw_observable V a ha ha1 hdec L j F hFm hFDm hFD
    (‖K‖^2) (2*‖K‖^2) (by positivity) (by positivity) hFb
    (fun Q z=>cascadePosteriorRetainedSquare_differential_bound V a ha ha1 hdec L j i K Q z) H

theorem integrable_cascadePosterior_retained_square_differential (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K H : FiniteStateField S) :
    Integrable (fun z=>fderiv ℝ (fun Q=>cascadePosteriorRetainedSquare V a L j i K Q z) H+
      cascadePosteriorRetainedSquare V a L j i K H z •
        fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L j Q z) H)
      (cascadePosteriorGaussianLaw V a L j H) := by
  haveI:=cascadePosteriorGaussianLaw_probability V a ha L j H
  have hs : ContDiff ℝ ∞ (fun z : (Fin j→Field n)×FiniteStateField S=>
      cascadePosteriorRetainedSquare V a L j i K z.2 (z.1,Classical.choice inferInstance)) :=
    (contDiff_cascadePosteriorRetainedMean V a ha L j i K).pow 2
  have hm : Measurable (fun z : (Fin j→Field n)×S=>
      fderiv ℝ (fun Q=>cascadePosteriorRetainedSquare V a L j i K Q z) H) := by
    apply measurable_from_prod_countable_left
    intro σ
    have hd : Continuous (fun z : (Fin j→Field n)×FiniteStateField S=>
        fderiv ℝ (fun Q=>cascadePosteriorRetainedSquare V a L j i K Q
          (z.1,Classical.choice inferInstance)) z.2) :=
      continuous_iff_continuousAt.mpr fun z=>
        (contDiffAt_partial_fderiv _ z hs.contDiffAt).continuousAt
    exact (hd.comp (continuous_id.prodMk (continuous_const (y:=H)))).measurable
  have hFm : Measurable (cascadePosteriorRetainedSquare V a L j i K H) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact (hs.continuous.comp (continuous_id.prodMk continuous_const)).measurable
  apply Integrable.of_bound (hm.add (hFm.smul
    (measurable_cascadePosterior_initialDifferential V a ha L j H))).aestronglyMeasurable (4*‖K‖^2)
  exact .of_forall fun z=>by
    change ‖fderiv ℝ (fun Q=>cascadePosteriorRetainedSquare V a L j i K Q z) H+
      cascadePosteriorRetainedSquare V a L j i K H z •
        fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L j Q z) H‖≤4*‖K‖^2
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    have hm:=cascadePosteriorRetainedMean_bound V a ha L j i K H z
    have hsq : |cascadePosteriorRetainedSquare V a L j i K H z|≤‖K‖^2 := by
      simpa only [cascadePosteriorRetainedSquare,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hm 2
    have hdl : ‖fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L j Q z) H‖≤2 := by
      rw [←norm_iteratedFDeriv_one]
      exact norm_cascadePosteriorLogDensity_firstJet_le_two V a ha ha1 hdec L j H z
    have hh:=add_le_add
      (cascadePosteriorRetainedSquare_differential_bound V a ha ha1 hdec L j i K H z)
      (mul_le_mul hsq hdl (norm_nonneg _) (by positivity))
    convert hh using 1 <;> ring

theorem fderiv_cascadePosterior_retained_square_stieltjes (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N i : ℕ) (K H W : FiniteStateField S) :
    fderiv ℝ (fun Q=>∫z,cascadePosteriorRetainedSquare V a L (N+1) i K Q z
      ∂cascadePosteriorGaussianLaw V a L (N+1) Q) H W=
      ∫z,fderiv ℝ (fun Q=>cascadePosteriorRetainedSquare V a L (N+1) i K Q z) H W+
        cascadePosteriorRetainedSquare V a L (N+1) i K H z*
          cavityFinitePosteriorScore V a L N H W z
        ∂cascadePosteriorGaussianLaw V a L (N+1) H := by
  rw [(hasFDerivAt_cascadePosterior_retained_square V a ha ha1 hdec L (N+1) i K H).fderiv,
    ContinuousLinearMap.integral_apply
      (integrable_cascadePosterior_retained_square_differential V a ha ha1 hdec L (N+1) i K H) W]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    fderiv_cascadePosteriorLogDensity_stieltjes V a ha L]

end QuantitativeFollowup
