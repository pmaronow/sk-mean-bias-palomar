module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseObservableData
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

/-! The actual terminal-feature jets commute with the coupling derivatives.
The second coupling response of a spin mean is the spatial derivative of
the actual second coupling response of the finite potential. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped ContDiff
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem directional_fderiv_evaluate (F : E→ℝ) (hF : ContDiff ℝ ∞ F)
    (H b K : E) :
    fderiv ℝ (fun Q=>fderiv ℝ F Q b) H K=fderiv ℝ (fderiv ℝ F) H K b :=by
  have hdF : ContDiff ℝ ∞ (fderiv ℝ F):=hF.fderiv_right (by simp)
  rw [((hdF.differentiable (by simp) H).hasFDerivAt.clm_apply
    (hasFDerivAt_const b H)).fderiv]
  simp

theorem cavity_directional_second_symmetry (F : E→ℝ) (hF : ContDiff ℝ ∞ F)
    (H b K : E) :
    fderiv ℝ (fun Q=>fderiv ℝ F Q b) H K=
      fderiv ℝ (fun Q=>fderiv ℝ F Q K) H b :=by
  rw [directional_fderiv_evaluate F hF H b K,directional_fderiv_evaluate F hF H K b]
  exact hF.contDiffAt.isSymmSndFDerivAt (by simp) K b

theorem cavity_directional_third_exchange (F : E→ℝ) (hF : ContDiff ℝ ∞ F)
    (H b K : E) :
    fderiv ℝ (fun Q=>fderiv ℝ (fun R=>fderiv ℝ F R b) Q K) H K=
      fderiv ℝ (fun Q=>fderiv ℝ (fun R=>fderiv ℝ F R K) Q K) H b :=by
  have he : (fun Q=>fderiv ℝ (fun R=>fderiv ℝ F R b) Q K)=
      fun Q=>fderiv ℝ (fun R=>fderiv ℝ F R K) Q b :=
    funext fun Q=>cavity_directional_second_symmetry F hF Q b K
  rw [he]
  exact cavity_directional_second_symmetry (fun Q=>fderiv ℝ F Q K)
    ((hF.fderiv_right (by simp)).clm_apply contDiff_const) H b K

variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}

theorem cavityFiniteEnergyFeatureMean_first_exchange (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (H b K : FiniteStateField S) :
    fderiv ℝ (cavityFiniteEnergyFeatureMean V a L j b) H K=
      fderiv ℝ (cavityFiniteEnergyFeatureMean V a L j K) H b :=
  cavity_directional_second_symmetry _ (contDiff_finiteStateGaussianTerminalCascade V a ha L j) H b K

theorem cavityFiniteEnergyFeatureMean_second_exchange (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (H b K : FiniteStateField S) :
    fderiv ℝ (fun Q=>fderiv ℝ (cavityFiniteEnergyFeatureMean V a L j b) Q K) H K=
      fderiv ℝ (fun Q=>fderiv ℝ (cavityFiniteEnergyFeatureMean V a L j K) Q K) H b :=
  cavity_directional_third_exchange _ (contDiff_finiteStateGaussianTerminalCascade V a ha L j) H b K

theorem cavityFiniteEnergyFeatureSquare_first (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (H b K : FiniteStateField S) :
    fderiv ℝ (fun Q=>(cavityFiniteEnergyFeatureMean V a L j b Q)^2) H K=
      2*cavityFiniteEnergyFeatureMean V a L j b H*
        fderiv ℝ (cavityFiniteEnergyFeatureMean V a L j b) H K :=by
  have hF:=(boundedJets_cavityFiniteEnergyFeatureMean V a ha L j b).1
  rw [((hF.differentiable (by simp) H).hasFDerivAt.pow 2).fderiv]
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,ContinuousLinearMap.smul_apply,
    smul_eq_mul,nsmul_eq_mul]

theorem cavityFiniteEnergyFeatureSquare_second (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (H b K : FiniteStateField S) :
    fderiv ℝ (fun Q=>fderiv ℝ
      (fun R=>(cavityFiniteEnergyFeatureMean V a L j b R)^2) Q K) H K=
      2*(fderiv ℝ (cavityFiniteEnergyFeatureMean V a L j b) H K)^2+
      2*cavityFiniteEnergyFeatureMean V a L j b H*
        fderiv ℝ (fun Q=>fderiv ℝ (cavityFiniteEnergyFeatureMean V a L j b) Q K) H K :=by
  let F:=cavityFiniteEnergyFeatureMean V a L j b
  have hF:=(boundedJets_cavityFiniteEnergyFeatureMean V a ha L j b).1
  have hD : ContDiff ℝ ∞ (fun Q=>fderiv ℝ F Q K):=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  have he : (fun Q=>fderiv ℝ (fun R=>(F R)^2) Q K)=
      fun Q=>2*F Q*fderiv ℝ F Q K :=
    funext fun Q=>cavityFiniteEnergyFeatureSquare_first V a ha L j Q b K
  have hresp:=((((hF.differentiable (by simp) H).hasFDerivAt.const_mul 2).mul
    ((hD.differentiable (by simp) H).hasFDerivAt))).fderiv
  simp only [Pi.mul_def] at hresp
  rw [he,hresp]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  change _=2*(fderiv ℝ F H K)^2+2*F H*fderiv ℝ (fun Q=>fderiv ℝ F Q K) H K
  ring

end QuantitativeFollowup
