module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterCovarianceIntegral

@[expose] public section

/-! Literal moving-observable Hessian expansion of the complete normalized
outer covariance. The density's two log jets and the two actual mean-gradient
corrections are retained. No response of the physical covariance is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ContDiff
namespace QuantitativeFollowup
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

private theorem centered_product_first (f g : E→ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (c d : ℝ) (x K : E) :
    fderiv ℝ (fun y=>(f y-c)*(g y-d)) x K=
      fderiv ℝ f x K*(g x-d)+(f x-c)*fderiv ℝ g x K :=by
  have he:=(((hf.differentiable (by simp) x).hasFDerivAt.sub_const c).mul
    ((hg.differentiable (by simp) x).hasFDerivAt.sub_const d)).fderiv
  simp only [Pi.sub_def,Pi.mul_def] at he
  rw [he]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

private theorem centered_product_second (f g : E→ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (c d : ℝ) (x K : E) :
    exponentialDensityHessian (fun y=>(f y-c)*(g y-d)) x K K=
      exponentialDensityHessian f x K K*(g x-d)+
      (f x-c)*exponentialDensityHessian g x K K+
      2*fderiv ℝ f x K*fderiv ℝ g x K :=by
  have hdF:=hasFDerivAt_exponential_directional_field f (hf.of_le (by simp)) x K
  have hdG:=hasFDerivAt_exponential_directional_field g (hg.of_le (by simp)) x K
  have hh : ContDiff ℝ 2 (fun y=>(f y-c)*(g y-d)):=
    ((hf.sub contDiff_const).mul (hg.sub contDiff_const)).of_le (by simp)
  have he : (fun y=>fderiv ℝ (fun z=>(f z-c)*(g z-d)) y K)=
      fun y=>fderiv ℝ f y K*(g y-d)+(f y-c)*fderiv ℝ g y K:=
    funext fun y=>centered_product_first f g hf hg c d y K
  have hl:=hasFDerivAt_exponential_directional_field _ hh x K
  rw [he] at hl
  have hr:=(hdF.mul ((hg.differentiable (by simp) x).hasFDerivAt.sub_const d)).add
    (((hf.differentiable (by simp) x).hasFDerivAt.sub_const c).mul hdG)
  have hD:=congrArg (fun T : E→L[ℝ]ℝ=>T K) (hl.unique hr)
  simp only [ContinuousLinearMap.flip_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul] at hD
  rw [hD]
  ring

variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}

theorem second_fderiv_cavityOuterPosteriorCovariance_expanded
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f g : FiniteStateField S→ℝ) (hf : BoundedJets f) (hg : BoundedJets g)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) (H K : FiniteStateField S) :
    let c:=cavityOuterPosteriorMean V a L s N R f W H
    let d:=cavityOuterPosteriorMean V a L s N R g W H
    fderiv ℝ (fun Q=>fderiv ℝ (cavityOuterPosteriorCovariance V a L s N R f g W) Q K) H K=
      (∫p,
        let F:=fun Q=>f (Q+R p.1+W p.2.1)
        let G:=fun Q=>g (Q+R p.1+W p.2.1)
        let score:=fderiv ℝ (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H K
        let secondScore:=exponentialDensityHessian
          (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H K K
        exponentialDensityHessian F H K K*(G H-d)+
          (F H-c)*exponentialDensityHessian G H K K+
          2*fderiv ℝ F H K*fderiv ℝ G H K+
          2*score*(fderiv ℝ F H K*(G H-d)+(F H-c)*fderiv ℝ G H K)+
          (F H-c)*(G H-d)*(secondScore+score^2)
        ∂cavityOuterPosteriorLaw V a L s N R H)-
      2*fderiv ℝ (cavityOuterPosteriorMean V a L s N R f W) H K*
        fderiv ℝ (cavityOuterPosteriorMean V a L s N R g W) H K :=by
  dsimp only
  rw [second_fderiv_cavityOuterPosteriorCovariance_integral V a ha ha1 hdec L s N R f g hf hg W H K]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun p=>by
    let F:=fun Q=>f (Q+R p.1+W p.2.1)
    let G:=fun Q=>g (Q+R p.1+W p.2.1)
    have hF:ContDiff ℝ ∞ F:=hf.1.comp ((contDiff_id.add contDiff_const).add contDiff_const)
    have hG:ContDiff ℝ ∞ G:=hg.1.comp ((contDiff_id.add contDiff_const).add contDiff_const)
    dsimp only [cavityOuterPosteriorCenteredProduct]
    rw [centered_product_first F G hF hG,centered_product_second F G hF hG]
    ring

end QuantitativeFollowup
