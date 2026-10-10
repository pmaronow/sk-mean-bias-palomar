module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterCovariance

@[expose] public section

/-! Exact integral response of the genuine complete outer covariance.
Both observables move with the field and the two mean-gradient correction
is retained. The centered observable is constructed from the actual means. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityOuterPosteriorCenteredProduct (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f g : FiniteStateField S→ℝ) (W : (Fin N→Field n)→L[ℝ]FiniteStateField S)
    (H x : FiniteStateField S) : ℝ :=
  (f x-cavityOuterPosteriorMean V a L s N R f W H)*
    (g x-cavityOuterPosteriorMean V a L s N R g W H)

theorem boundedJets_cavityOuterPosteriorCenteredProduct
    (V : S→ℝ) (a : ℕ→ℝ) (L : ℕ→Field n→L[ℝ]FiniteStateField S)
    (s : ℝ) (N : ℕ) (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f g : FiniteStateField S→ℝ) (hf : BoundedJets f) (hg : BoundedJets g)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    BoundedJets (cavityOuterPosteriorCenteredProduct V a L s N R f g W H) :=by
  change BoundedJets (fun x=>(f x-cavityOuterPosteriorMean V a L s N R f W H)*
    (g x-cavityOuterPosteriorMean V a L s N R g W H))
  simpa only [sub_eq_add_neg,Pi.add_def,Pi.mul_def] using
    (hf.add (boundedJets_const (-cavityOuterPosteriorMean V a L s N R f W H))).mul
      (hg.add (boundedJets_const (-cavityOuterPosteriorMean V a L s N R g W H)))

theorem second_fderiv_cavityOuterPosteriorCovariance_integral
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f g : FiniteStateField S→ℝ) (hf : BoundedJets f) (hg : BoundedJets g)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) (H K : FiniteStateField S) :
    let h:=cavityOuterPosteriorCenteredProduct V a L s N R f g W H
    fderiv ℝ (fun Q=>fderiv ℝ (cavityOuterPosteriorCovariance V a L s N R f g W) Q K) H K=
      (∫p,exponentialDensityHessian (fun Q=>h (Q+R p.1+W p.2.1)) H K K+
        2*fderiv ℝ (fun Q=>h (Q+R p.1+W p.2.1)) H K*
          fderiv ℝ (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H K+
        h (H+R p.1+W p.2.1)*
          (exponentialDensityHessian (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H K K+
            (fderiv ℝ (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H K)^2)
        ∂cavityOuterPosteriorLaw V a L s N R H)-
      2*fderiv ℝ (cavityOuterPosteriorMean V a L s N R f W) H K*
        fderiv ℝ (cavityOuterPosteriorMean V a L s N R g W) H K :=by
  dsimp only
  let h:=cavityOuterPosteriorCenteredProduct V a L s N R f g W H
  have hh:=boundedJets_cavityOuterPosteriorCenteredProduct V a L s N R f g hf hg W H
  have hM:=contDiff_cavityOuterPosteriorMean V a ha ha1 hdec L s N R h hh W
  have he : fderiv ℝ (fun Q=>fderiv ℝ (cavityOuterPosteriorMean V a L s N R h W) Q K) H K=
      exponentialDensityHessian (cavityOuterPosteriorMean V a L s N R h W) H K K :=by
    rw [(hasFDerivAt_exponential_directional_field _ (hM.of_le (by simp)) H K).fderiv,
      ContinuousLinearMap.flip_apply]
  rw [second_fderiv_cavityOuterPosteriorCovariance V a ha ha1 hdec L s N R f g hf hg W H K]
  change fderiv ℝ (fun Q=>fderiv ℝ (cavityOuterPosteriorMean V a L s N R h W) Q K) H K-_= _
  rw [he,second_fderiv_cavityOuterPosteriorMean V a ha ha1 hdec L s N R h hh W H K]

end QuantitativeFollowup
