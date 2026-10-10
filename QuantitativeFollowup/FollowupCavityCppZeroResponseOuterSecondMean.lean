module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterIntegralJets
public import FourPapersCommon.ExponentialDensityHessian

@[expose] public section

/-! The genuine second retained-observable response under the full outer
posterior, including the outer normalizer's first and second log jets. -/
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

theorem second_fderiv_cavityOuterPosteriorMean
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) (H K : FiniteStateField S) :
    exponentialDensityHessian (cavityOuterPosteriorMean V a L s N R f W) H K K=
      ∫p,exponentialDensityHessian (fun Q=>f (Q+R p.1+W p.2.1)) H K K+
        2*fderiv ℝ (fun Q=>f (Q+R p.1+W p.2.1)) H K*
          fderiv ℝ (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H K+
        f (H+R p.1+W p.2.1)*
          (exponentialDensityHessian (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H K K+
            (fderiv ℝ (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H K)^2)
        ∂cavityOuterPosteriorLaw V a L s N R H :=by
  have hj:=cavityOuterPosteriorMean_iteratedFDeriv_integral V a ha ha1 hdec L s N 2 R f hf W H
  have he:=congrArg
    (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 2=>FiniteStateField S) ℝ=>T (fun _=>K)) hj.2
  rw [ContinuousMultilinearMap.integral_apply hj.1] at he
  simp only [iteratedFDeriv_two_apply] at he
  rw [integral_cavityOuterPosteriorLaw_exp V a ha L s N R H]
  change (fderiv ℝ (fderiv ℝ (cavityOuterPosteriorMean V a L s N R f W)) H K) K=_
  rw [he]
  apply integral_congr_ae
  exact .of_forall fun p=>by
    have hLc:ContDiff ℝ 2 (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p):=
      ((contDiff_cavityOuterPosteriorLogDensity_joint V a ha L s N R p.2.2).comp
        (contDiff_id.prodMk (contDiff_const (c:=(p.1,p.2.1))))).of_le (by simp)
    have hFc:ContDiff ℝ 2 (fun Q=>f (Q+R p.1+W p.2.1)):=
      (hf.1.comp ((contDiff_id.add contDiff_const).add contDiff_const)).of_le (by simp)
    change exponentialDensityHessian
      (fun Q=>Real.exp (cavityOuterPosteriorLogDensity V a L s N R Q p)*f (Q+R p.1+W p.2.1)) H K K=_
    rw [exponentialDensityHessian_exp_mul_observable _ _ hLc hFc]
    simp only [smul_eq_mul]
    ring

end QuantitativeFollowup
