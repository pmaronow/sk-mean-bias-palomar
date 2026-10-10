module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterSecondMean

@[expose] public section

/-! Actual covariance differentiation under the complete outer posterior,
with both retained-field observables moving with the initial field. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityOuterPosteriorCovariance (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f g : FiniteStateField S→ℝ) (W : (Fin N→Field n)→L[ℝ]FiniteStateField S)
    (H : FiniteStateField S) : ℝ :=
  covariance (fun z=>f (H+R z.1+W z.2.1)) (fun z=>g (H+R z.1+W z.2.1))
    (cavityOuterPosteriorLaw V a L s N R H)

theorem cavityOuterPosteriorCovariance_eq_centeredMean
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f g : FiniteStateField S→ℝ) (hf : BoundedJets f) (hg : BoundedJets g)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S)
    (c d : ℝ) (Q : FiniteStateField S) :
    cavityOuterPosteriorCovariance V a L s N R f g W Q=
      cavityOuterPosteriorMean V a L s N R (fun x=>(f x-c)*(g x-d)) W Q-
        (cavityOuterPosteriorMean V a L s N R f W Q-c)*
        (cavityOuterPosteriorMean V a L s N R g W Q-d) :=by
  haveI:=cavityOuterPosteriorLaw_probability V a ha L s N R Q
  obtain ⟨B,hB,hfb⟩:=hf.2 0
  obtain ⟨C,hC,hgb⟩:=hg.2 0
  have hmF : MemLp (fun z=>f (Q+R z.1+W z.2.1)) 2 (cavityOuterPosteriorLaw V a L s N R Q) :=
    MemLp.of_bound (hf.1.continuous.measurable.comp (show Measurable (fun z : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>Q+R z.1+W z.2.1) from by fun_prop)).aestronglyMeasurable B
      (.of_forall fun z=>by simpa only [norm_iteratedFDeriv_zero] using hfb (Q+R z.1+W z.2.1))
  have hmG : MemLp (fun z=>g (Q+R z.1+W z.2.1)) 2 (cavityOuterPosteriorLaw V a L s N R Q) :=
    MemLp.of_bound (hg.1.continuous.measurable.comp (show Measurable (fun z : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>Q+R z.1+W z.2.1) from by fun_prop)).aestronglyMeasurable C
      (.of_forall fun z=>by simpa only [norm_iteratedFDeriv_zero] using hgb (Q+R z.1+W z.2.1))
  have hiF:=hmF.integrable (by norm_num)
  have hiG:=hmG.integrable (by norm_num)
  have hc:=covariance_eq_sub (hmF.sub (memLp_const c)) (hmG.sub (memLp_const d))
  simp only [Pi.sub_def,Pi.mul_def] at hc
  rw [covariance_sub_const_left hiF c,covariance_sub_const_right hiG d] at hc
  simpa only [cavityOuterPosteriorCovariance,cavityOuterPosteriorMean,Pi.mul_apply,
    Pi.sub_apply,integral_sub hiF (integrable_const c),integral_sub hiG (integrable_const d),
    integral_const,probReal_univ,one_smul] using hc

theorem second_fderiv_cavityOuterPosteriorCovariance
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f g : FiniteStateField S→ℝ) (hf : BoundedJets f) (hg : BoundedJets g)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S)
    (H K : FiniteStateField S) :
    fderiv ℝ (fun Q=>fderiv ℝ (cavityOuterPosteriorCovariance V a L s N R f g W) Q K) H K=
      fderiv ℝ (fun Q=>fderiv ℝ (cavityOuterPosteriorMean V a L s N R
        (fun x=>(f x-cavityOuterPosteriorMean V a L s N R f W H)*
          (g x-cavityOuterPosteriorMean V a L s N R g W H)) W) Q K) H K-
      2*fderiv ℝ (cavityOuterPosteriorMean V a L s N R f W) H K*
        fderiv ℝ (cavityOuterPosteriorMean V a L s N R g W) H K :=by
  let Mf:=cavityOuterPosteriorMean V a L s N R f W
  let Mg:=cavityOuterPosteriorMean V a L s N R g W
  let h:=fun x=>(f x-Mf H)*(g x-Mg H)
  let Mh:=cavityOuterPosteriorMean V a L s N R h W
  have hh : BoundedJets h :=by
    simpa only [h,sub_eq_add_neg] using
      (hf.add (boundedJets_const (-Mf H))).mul (hg.add (boundedJets_const (-Mg H)))
  have hdf (Q):=(contDiff_cavityOuterPosteriorMean V a ha ha1 hdec L s N R f hf W).differentiable (by simp) Q |>.hasFDerivAt
  have hdg (Q):=(contDiff_cavityOuterPosteriorMean V a ha ha1 hdec L s N R g hg W).differentiable (by simp) Q |>.hasFDerivAt
  have hdh (Q):=(contDiff_cavityOuterPosteriorMean V a ha ha1 hdec L s N R h hh W).differentiable (by simp) Q |>.hasFDerivAt
  have he : cavityOuterPosteriorCovariance V a L s N R f g W=
      fun Q=>Mh Q-(Mf Q-Mf H)*(Mg Q-Mg H) :=by
    funext Q
    exact cavityOuterPosteriorCovariance_eq_centeredMean V a ha L s N R f g hf hg W _ _ Q
  have hfirst (Q) : fderiv ℝ (cavityOuterPosteriorCovariance V a L s N R f g W) Q K=
      fderiv ℝ Mh Q K-(fderiv ℝ Mf Q K*(Mg Q-Mg H)+(Mf Q-Mf H)*fderiv ℝ Mg Q K) :=by
    have hd:=((hdh Q).sub (((hdf Q).sub_const (Mf H)).mul ((hdg Q).sub_const (Mg H)))).fderiv
    simp only [Pi.sub_def,Pi.mul_def] at hd
    rw [he,hd]
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,smul_eq_mul,Mf,Mg,Mh]
    ring
  have hdDf:=(((contDiff_cavityOuterPosteriorMean V a ha ha1 hdec L s N R f hf W).fderiv_right (m:=∞) (by simp)).clm_apply (contDiff_const (c:=K))).differentiable (by simp) H |>.hasFDerivAt
  have hdDg:=(((contDiff_cavityOuterPosteriorMean V a ha ha1 hdec L s N R g hg W).fderiv_right (m:=∞) (by simp)).clm_apply (contDiff_const (c:=K))).differentiable (by simp) H |>.hasFDerivAt
  have hdDh:=(((contDiff_cavityOuterPosteriorMean V a ha ha1 hdec L s N R h hh W).fderiv_right (m:=∞) (by simp)).clm_apply (contDiff_const (c:=K))).differentiable (by simp) H |>.hasFDerivAt
  have hresp:=(hdDh.sub ((hdDf.mul ((hdg H).sub_const (Mg H))).add
    (((hdf H).sub_const (Mf H)).mul hdDg))).fderiv
  simp only [Pi.sub_def,Pi.mul_def,Pi.add_def] at hresp
  have hfun : (fun Q=>fderiv ℝ (cavityOuterPosteriorCovariance V a L s N R f g W) Q K)=
      fun Q=>fderiv ℝ Mh Q K-(fderiv ℝ Mf Q K*(Mg Q-Mg H)+(Mf Q-Mf H)*fderiv ℝ Mg Q K) :=funext hfirst
  rw [hfun,hresp]
  simp only [Mf,Mg,Mh,sub_self,zero_smul,zero_mul,mul_zero,add_zero,zero_add,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring


end QuantitativeFollowup
