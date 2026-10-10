module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterLogJetIntegrability
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterCovarianceExpansion

@[expose] public section

/-! Honest integrability of the separate moving-observable response terms.
The density and observable jets are actual evaluated jets, with their
uniform bounds derived from the normalized Gaussian posterior. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ContDiff
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem memLp_cavityOuterPosterior_translatedFieldJet
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N r : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S)
    (H : FiniteStateField S) (b : Fin r→FiniteStateField S) (q : ENNReal) :
    MemLp (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
      iteratedFDeriv ℝ r (fun Q=>f (Q+R p.1+W p.2.1)) H b)
      q (cavityOuterPosteriorLaw V a L s N R H) :=by
  refine MemLp.ae_eq ?_ (memLp_cavityOuterPosterior_fieldJetApply V a ha L s N r R f hf W H b q)
  exact .of_forall fun p=>by
    change iteratedFDeriv ℝ r f (H+R p.1+W p.2.1) b=
      iteratedFDeriv ℝ r (fun Q=>f (Q+R p.1+W p.2.1)) H b
    have he:(fun Q=>f (Q+R p.1+W p.2.1))=fun Q=>f (Q+(R p.1+W p.2.1)):=by funext Q;rw [add_assoc]
    rw [he,iteratedFDeriv_comp_add_right,←add_assoc]

theorem integrable_cavityOuterPosterior_responseIntegrand
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f g : FiniteStateField S→ℝ) (hf : BoundedJets f) (hg : BoundedJets g)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) (H K : FiniteStateField S) (c d : ℝ) :
    Integrable (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
      let F:=fun Q=>f (Q+R p.1+W p.2.1)
      let G:=fun Q=>g (Q+R p.1+W p.2.1)
      let score:=fderiv ℝ (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H K
      let secondScore:=exponentialDensityHessian (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H K K
      exponentialDensityHessian F H K K*(G H-d)+(F H-c)*exponentialDensityHessian G H K K+
        2*fderiv ℝ F H K*fderiv ℝ G H K+
        2*score*(fderiv ℝ F H K*(G H-d)+(F H-c)*fderiv ℝ G H K)+
        (F H-c)*(G H-d)*(secondScore+score^2))
      (cavityOuterPosteriorLaw V a L s N R H) :=by
  haveI:=cavityOuterPosteriorLaw_probability V a ha L s N R H
  have f0:MemLp (fun p=>f (H+R p.1+W p.2.1)-c) (⊤ : ENNReal) (cavityOuterPosteriorLaw V a L s N R H):=
    (memLp_cavityOuterPosterior_fieldValue V a ha L s N R f hf W H (⊤ : ENNReal)).sub (memLp_const c)
  have g0:MemLp (fun p=>g (H+R p.1+W p.2.1)-d) (⊤ : ENNReal) (cavityOuterPosteriorLaw V a L s N R H):=
    (memLp_cavityOuterPosterior_fieldValue V a ha L s N R g hg W H (⊤ : ENNReal)).sub (memLp_const d)
  have f1:MemLp (fun p=>fderiv ℝ (fun Q=>f (Q+R p.1+W p.2.1)) H K) (⊤ : ENNReal)
      (cavityOuterPosteriorLaw V a L s N R H):=by
    simpa only [iteratedFDeriv_one_apply] using
      memLp_cavityOuterPosterior_translatedFieldJet V a ha L s N 1 R f hf W H (fun _=>K) (⊤ : ENNReal)
  have g1:MemLp (fun p=>fderiv ℝ (fun Q=>g (Q+R p.1+W p.2.1)) H K) (⊤ : ENNReal)
      (cavityOuterPosteriorLaw V a L s N R H):=by
    simpa only [iteratedFDeriv_one_apply] using
      memLp_cavityOuterPosterior_translatedFieldJet V a ha L s N 1 R g hg W H (fun _=>K) (⊤ : ENNReal)
  have f2:MemLp (fun p=>exponentialDensityHessian (fun Q=>f (Q+R p.1+W p.2.1)) H K K) (⊤ : ENNReal)
      (cavityOuterPosteriorLaw V a L s N R H):=by
    simpa only [iteratedFDeriv_two_apply,exponentialDensityHessian] using
      memLp_cavityOuterPosterior_translatedFieldJet V a ha L s N 2 R f hf W H (fun _=>K) (⊤ : ENNReal)
  have g2:MemLp (fun p=>exponentialDensityHessian (fun Q=>g (Q+R p.1+W p.2.1)) H K K) (⊤ : ENNReal)
      (cavityOuterPosteriorLaw V a L s N R H):=by
    simpa only [iteratedFDeriv_two_apply,exponentialDensityHessian] using
      memLp_cavityOuterPosterior_translatedFieldJet V a ha L s N 2 R g hg W H (fun _=>K) (⊤ : ENNReal)
  have hs:=memLp_cavityOuterPosterior_score V a ha ha1 hdec L s N R H K (⊤ : ENNReal)
  have hss:=memLp_cavityOuterPosterior_secondScore V a ha ha1 hdec L s N R H K (⊤ : ENNReal)
  have hsum:MemLp _ (⊤ : ENNReal) (cavityOuterPosteriorLaw V a L s N R H):=
    ((((f2.mul (r:=(⊤:ENNReal)) g0).add (f0.mul (r:=(⊤:ENNReal)) g2)).add
      ((f1.const_mul 2).mul (r:=(⊤:ENNReal)) g1)).add
      ((hs.const_mul 2).mul (r:=(⊤:ENNReal)) ((f1.mul (r:=(⊤:ENNReal)) g0).add
        (f0.mul (r:=(⊤:ENNReal)) g1)))).add
      ((f0.mul (r:=(⊤:ENNReal)) g0).mul (r:=(⊤:ENNReal))
        (hss.add (hs.mul (r:=(⊤:ENNReal)) hs)))
  simpa only [Pi.mul_def,Pi.add_def,pow_two] using hsum.integrable (by simp)

end QuantitativeFollowup
