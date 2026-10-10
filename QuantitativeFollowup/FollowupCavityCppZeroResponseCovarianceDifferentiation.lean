module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseObservableData
public import Mathlib.Probability.Moments.Covariance

@[expose] public section

/-! Covariance differentiation under the actual normalized finite posterior.
The centering constants are fixed at the differentiation point. Both the
observable and the probability law vary; all their regularity is proved from
the bounded jets of the observable and the actual posterior density. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityPosteriorTranslatedMean (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (f : FiniteStateField S→ℝ) (W : ((Fin j→Field n)×S)→FiniteStateField S)
    (H : FiniteStateField S) : ℝ :=
  ∫z,f (H+W z)∂cascadePosteriorGaussianLaw V a L j H

theorem hasFDerivAt_cavityPosteriorTranslatedMean
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : ((Fin j→Field n)×S)→FiniteStateField S) (hW : Measurable W)
    (H : FiniteStateField S) :
    HasFDerivAt (cavityPosteriorTranslatedMean V a L j f W)
      (fderiv ℝ (cavityPosteriorTranslatedMean V a L j f W) H) H :=by
  let d:=cavityPosteriorTranslatedC2Data f hf W hW
  exact (hasFDerivAt_cascadePosteriorGaussianLaw_observable V a ha ha1 hdec L j _
    d.measurable_value d.measurable_first
    (fun z Q=>(d.smooth z).differentiable (by norm_num) Q)
    d.bound d.firstBound d.bound_nonneg d.firstBound_nonneg d.value_bound d.first_bound H).differentiableAt.hasFDerivAt

theorem hasFDerivAt_cavityPosteriorTranslatedMean_directional
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : ((Fin j→Field n)×S)→FiniteStateField S) (hW : Measurable W)
    (H K : FiniteStateField S) :
    HasFDerivAt (fun Q=>fderiv ℝ (cavityPosteriorTranslatedMean V a L j f W) Q K)
      (fderiv ℝ (fun Q=>fderiv ℝ (cavityPosteriorTranslatedMean V a L j f W) Q K) H) H :=by
  let d:=cavityPosteriorTranslatedC2Data f hf W hW
  exact (hasFDerivAt_cascadePosteriorGaussianLaw_observable_directional_first V a ha ha1 hdec L j _
    d.measurable_value d.measurable_first d.measurable_second d.smooth
    d.bound d.firstBound d.secondBound d.bound_nonneg d.firstBound_nonneg d.secondBound_nonneg
    d.value_bound d.first_bound d.second_bound H K).differentiableAt.hasFDerivAt

def cavityPosteriorTranslatedCovariance (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (f g : FiniteStateField S→ℝ) (W : ((Fin j→Field n)×S)→FiniteStateField S)
    (H : FiniteStateField S) : ℝ :=
  covariance (fun z=>f (H+W z)) (fun z=>g (H+W z))
    (cascadePosteriorGaussianLaw V a L j H)

theorem cavityPosteriorTranslatedCovariance_eq_centeredMean
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (f g : FiniteStateField S→ℝ) (hf : BoundedJets f) (hg : BoundedJets g)
    (W : ((Fin j→Field n)×S)→FiniteStateField S) (hW : Measurable W)
    (c d : ℝ) (Q : FiniteStateField S) :
    cavityPosteriorTranslatedCovariance V a L j f g W Q=
      cavityPosteriorTranslatedMean V a L j (fun x=>(f x-c)*(g x-d)) W Q-
        (cavityPosteriorTranslatedMean V a L j f W Q-c)*
        (cavityPosteriorTranslatedMean V a L j g W Q-d) :=by
  haveI:=cascadePosteriorGaussianLaw_probability V a ha L j Q
  obtain ⟨B,hB,hfb⟩:=hf.2 0
  obtain ⟨C,hC,hgb⟩:=hg.2 0
  have hmF : MemLp (fun z=>f (Q+W z)) 2 (cascadePosteriorGaussianLaw V a L j Q) :=
    MemLp.of_bound (hf.1.continuous.measurable.comp (measurable_const.add hW)).aestronglyMeasurable B
      (.of_forall fun z=>by simpa only [norm_iteratedFDeriv_zero] using hfb (Q+W z))
  have hmG : MemLp (fun z=>g (Q+W z)) 2 (cascadePosteriorGaussianLaw V a L j Q) :=
    MemLp.of_bound (hg.1.continuous.measurable.comp (measurable_const.add hW)).aestronglyMeasurable C
      (.of_forall fun z=>by simpa only [norm_iteratedFDeriv_zero] using hgb (Q+W z))
  have hiF:=hmF.integrable (by norm_num)
  have hiG:=hmG.integrable (by norm_num)
  have hc:=covariance_eq_sub (hmF.sub (memLp_const c)) (hmG.sub (memLp_const d))
  simp only [Pi.sub_def,Pi.mul_def] at hc
  rw [covariance_sub_const_left hiF c,covariance_sub_const_right hiG d] at hc
  simpa only [cavityPosteriorTranslatedCovariance,cavityPosteriorTranslatedMean,Pi.mul_apply,
    Pi.sub_apply,integral_sub hiF (integrable_const c),integral_sub hiG (integrable_const d),
    integral_const,probReal_univ,one_smul] using hc

theorem second_fderiv_cavityPosteriorTranslatedCovariance
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (f g : FiniteStateField S→ℝ) (hf : BoundedJets f) (hg : BoundedJets g)
    (W : ((Fin j→Field n)×S)→FiniteStateField S) (hW : Measurable W)
    (H K : FiniteStateField S) :
    fderiv ℝ (fun Q=>fderiv ℝ (cavityPosteriorTranslatedCovariance V a L j f g W) Q K) H K=
      fderiv ℝ (fun Q=>fderiv ℝ (cavityPosteriorTranslatedMean V a L j
        (fun x=>(f x-cavityPosteriorTranslatedMean V a L j f W H)*
          (g x-cavityPosteriorTranslatedMean V a L j g W H)) W) Q K) H K-
      2*fderiv ℝ (cavityPosteriorTranslatedMean V a L j f W) H K*
        fderiv ℝ (cavityPosteriorTranslatedMean V a L j g W) H K :=by
  let Mf:=cavityPosteriorTranslatedMean V a L j f W
  let Mg:=cavityPosteriorTranslatedMean V a L j g W
  let h:=fun x=>(f x-Mf H)*(g x-Mg H)
  let Mh:=cavityPosteriorTranslatedMean V a L j h W
  have hh : BoundedJets h :=by
    simpa only [h,sub_eq_add_neg] using
      (hf.add (boundedJets_const (-Mf H))).mul (hg.add (boundedJets_const (-Mg H)))
  have hdf (Q):=hasFDerivAt_cavityPosteriorTranslatedMean V a ha ha1 hdec L j f hf W hW Q
  have hdg (Q):=hasFDerivAt_cavityPosteriorTranslatedMean V a ha ha1 hdec L j g hg W hW Q
  have hdh (Q):=hasFDerivAt_cavityPosteriorTranslatedMean V a ha ha1 hdec L j h hh W hW Q
  have he : cavityPosteriorTranslatedCovariance V a L j f g W=
      fun Q=>Mh Q-(Mf Q-Mf H)*(Mg Q-Mg H) :=by
    funext Q
    exact cavityPosteriorTranslatedCovariance_eq_centeredMean V a ha L j f g hf hg W hW _ _ Q
  have hfirst (Q) : fderiv ℝ (cavityPosteriorTranslatedCovariance V a L j f g W) Q K=
      fderiv ℝ Mh Q K-(fderiv ℝ Mf Q K*(Mg Q-Mg H)+(Mf Q-Mf H)*fderiv ℝ Mg Q K) :=by
    have hd:=((hdh Q).sub (((hdf Q).sub_const (Mf H)).mul ((hdg Q).sub_const (Mg H)))).fderiv
    simp only [Pi.sub_def,Pi.mul_def] at hd
    rw [he,hd]
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,smul_eq_mul,Mf,Mg,Mh]
    ring
  have hdDf:=hasFDerivAt_cavityPosteriorTranslatedMean_directional V a ha ha1 hdec L j f hf W hW H K
  have hdDg:=hasFDerivAt_cavityPosteriorTranslatedMean_directional V a ha ha1 hdec L j g hg W hW H K
  have hdDh:=hasFDerivAt_cavityPosteriorTranslatedMean_directional V a ha ha1 hdec L j h hh W hW H K
  have hresp:=(hdDh.sub ((hdDf.mul ((hdg H).sub_const (Mg H))).add
    (((hdf H).sub_const (Mf H)).mul hdDg))).fderiv
  simp only [Pi.sub_def,Pi.mul_def,Pi.add_def] at hresp
  have hfun : (fun Q=>fderiv ℝ (cavityPosteriorTranslatedCovariance V a L j f g W) Q K)=
      fun Q=>fderiv ℝ Mh Q K-(fderiv ℝ Mf Q K*(Mg Q-Mg H)+(Mf Q-Mf H)*fderiv ℝ Mg Q K) :=funext hfirst
  rw [hfun,hresp]
  simp only [Mf,Mg,Mh,sub_self,zero_smul,zero_mul,mul_zero,add_zero,zero_add,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

end QuantitativeFollowup
