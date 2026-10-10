module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeSquare

@[expose] public section

/-! Uniform initial-field modulus of the retained square differential,
derived from the actual third cascade jet. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem fderiv_cascadePosteriorRetainedMean_apply (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K H W : FiniteStateField S)
    (z : (Fin j→Field n)×S) :
    fderiv ℝ (fun Q=>cascadePosteriorRetainedMean V a L j i K Q z) H W=
      fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j-i)))
        (historyExtended (cascadePosteriorHistory L j H z.1) i) W K := by
  let U:=finiteStateGaussianTerminalCascade V a L (j-i)
  let w:=cascadePosteriorHistory L j 0 z.1 (Fin.ofNat (j+1) i)
  have he : (fun Q=>cascadePosteriorRetainedMean V a L j i K Q z)=
      fun Q=>fderiv ℝ U (Q+w) K := by
    funext Q
    unfold cascadePosteriorRetainedMean
    dsimp only [historyExtended]
    rw [cascadePosteriorHistory_eq_initial_add]
  let A : (FiniteStateField S→L[ℝ]ℝ)→L[ℝ]ℝ:=ContinuousLinearMap.apply ℝ ℝ K
  have hs:=(contDiff_finiteStateGaussianTerminalCascade V a ha L (j-i)).fderiv_right (m:=∞) (by simp)
  have hd:=(A.hasFDerivAt.comp H ((hs.differentiable (by simp) (H+w)).hasFDerivAt.comp H
    ((hasFDerivAt_id H).add_const w)))
  dsimp only [Function.comp_def,id_eq,A,U] at hd
  have hdEq : fderiv ℝ (fun Q=>fderiv ℝ U (Q+w) K) H=
      A.comp ((fderiv ℝ (fderiv ℝ U) (H+w)).comp (ContinuousLinearMap.id ℝ _)) := by
    simpa only [U,A,ContinuousLinearMap.apply_apply] using hd.fderiv
  rw [he,hdEq]
  simp only [A,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.id_apply]
  dsimp only [historyExtended]
  rw [cascadePosteriorHistory_eq_initial_add]

theorem finiteStateCascade_secondDifferential_lipschitz (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) :
    LipschitzWith 8 (fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j))) := by
  have hs:=((contDiff_finiteStateGaussianTerminalCascade V a ha L j).fderiv_right (m:=∞) (by simp)).fderiv_right
    (m:=∞) (by simp)
  apply lipschitzWith_of_nnnorm_fderiv_le (hs.differentiable (by simp))
  intro H
  rw [←NNReal.coe_le_coe,coe_nnnorm,←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv,
    norm_iteratedFDeriv_fderiv]
  exact norm_finiteStateCascade_thirdJet_le_eight V a ha ha1 hdec L j H

theorem cascadePosteriorRetainedMean_differential_lipschitz (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K : FiniteStateField S)
    (z : (Fin j→Field n)×S) :
    LipschitzWith (8*‖K‖₊) (fderiv ℝ (fun H=>cascadePosteriorRetainedMean V a L j i K H z)) := by
  apply LipschitzWith.of_dist_le_mul
  intro H Q
  rw [dist_eq_norm]
  apply (fderiv ℝ (fun H=>cascadePosteriorRetainedMean V a L j i K H z) H-
    fderiv ℝ (fun H=>cascadePosteriorRetainedMean V a L j i K H z) Q).opNorm_le_bound (by positivity)
  intro W
  rw [ContinuousLinearMap.sub_apply,fderiv_cascadePosteriorRetainedMean_apply V a ha,
    fderiv_cascadePosteriorRetainedMean_apply V a ha]
  dsimp only [historyExtended]
  rw [cascadePosteriorHistory_eq_initial_add L j H z.1,
    cascadePosteriorHistory_eq_initial_add L j Q z.1]
  let w:=cascadePosteriorHistory L j 0 z.1 (Fin.ofNat (j+1) i)
  let D:=fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j-i)))
  have hb:=(finiteStateCascade_secondDifferential_lipschitz V a ha ha1 hdec L (j-i)).norm_sub_le (H+w) (Q+w)
  simp only [NNReal.coe_ofNat,add_sub_add_right_eq_sub] at hb
  change ‖D (H+w) W K-D (Q+w) W K‖≤_
  rw [←ContinuousLinearMap.sub_apply,←ContinuousLinearMap.sub_apply]
  have hh:=(((D (H+w)-D (Q+w)) W).le_opNorm K).trans
    (mul_le_mul_of_nonneg_right ((D (H+w)-D (Q+w)).le_opNorm W) (norm_nonneg K))
  apply hh.trans
  have ht:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg W)) (norm_nonneg K)
  simpa only [NNReal.coe_mul,NNReal.coe_ofNat,coe_nnnorm,dist_eq_norm,mul_assoc,mul_comm,mul_left_comm] using ht

theorem cascadePosteriorRetainedSquare_differential_lipschitz (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K : FiniteStateField S)
    (z : (Fin j→Field n)×S) :
    LipschitzWith (18*‖K‖₊^2) (fderiv ℝ (fun H=>cascadePosteriorRetainedSquare V a L j i K H z)) := by
  let f:=fun H=>cascadePosteriorRetainedMean V a L j i K H z
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_cascadePosteriorRetainedMean V a ha L j i K).comp (contDiff_const.prodMk contDiff_id)
  have hd (H : FiniteStateField S) :
      fderiv ℝ (fun Q=>cascadePosteriorRetainedSquare V a L j i K Q z) H=(2*f H) • fderiv ℝ f H := by
    change fderiv ℝ (f^2) H=_
    rw [fderiv_pow 2 (hf.differentiable (by simp) H)]
    norm_num only [pow_one,nsmul_eq_mul,Nat.cast_ofNat,Nat.reduceSub]
  apply LipschitzWith.of_dist_le_mul
  intro H Q
  rw [dist_eq_norm,hd,hd]
  have he : (2*f H) • fderiv ℝ f H-(2*f Q) • fderiv ℝ f Q=
      (2*f H) • (fderiv ℝ f H-fderiv ℝ f Q)+(2*(f H-f Q)) • fderiv ℝ f Q := by
    module
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hm:=cascadePosteriorRetainedMean_bound V a ha L j i K H z
  have hdm:=(cascadePosteriorRetainedMean_differential_lipschitz V a ha ha1 hdec L j i K z).norm_sub_le H Q
  have hl:=(cascadePosteriorRetainedMean_lipschitz V a ha ha1 hdec L j i K z).norm_sub_le H Q
  have hb : ‖fderiv ℝ f Q‖≤‖K‖:=
    norm_fderiv_le_of_lipschitz ℝ (cascadePosteriorRetainedMean_lipschitz V a ha ha1 hdec L j i K z)
  simp only [NNReal.coe_mul,NNReal.coe_ofNat,coe_nnnorm,Real.norm_eq_abs] at hdm hl
  change |f H|≤‖K‖ at hm
  change ‖fderiv ℝ f H-fderiv ℝ f Q‖≤8*‖K‖*‖H-Q‖ at hdm
  change |f H-f Q|≤‖K‖*‖H-Q‖ at hl
  have h1 : (2*|f H|)*‖fderiv ℝ f H-fderiv ℝ f Q‖≤
      (2*‖K‖)*(8*‖K‖*‖H-Q‖) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤2)) hdm
      (norm_nonneg _) (by positivity)
  have h2 : (2*|f H-f Q|)*‖fderiv ℝ f Q‖≤(2*(‖K‖*‖H-Q‖))*‖K‖ :=
    mul_le_mul (mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ)≤2)) hb
      (norm_nonneg _) (by positivity)
  apply (add_le_add h1 h2).trans_eq
  simp only [NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_pow,coe_nnnorm,dist_eq_norm]
  ring

end QuantitativeFollowup
