module
public import QuantitativeFollowup.FollowupCavityMixtureOuterContinuity
public import QuantitativeFollowup.FollowupCavityMixtureUniformMeanJets
public import QuantitativeFollowup.FollowupCavityMixtureJointSpatial

@[expose] public section

/-! The full outer Gaussian numerators have genuine joint spatial C2 data
under a varying Gaussian input family. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology ContDiff
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {S P J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [TopologicalSpace P] [FirstCountableTopology P] {n : ℕ}

private instance cavityMixtureDual_complete : CompleteSpace (FiniteStateField S→L[ℝ]ℝ) :=
  ContinuousLinearMap.instCompleteSpace

theorem cavityOuterPosteriorLogNormalizer_jointSpatial_input_family
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀i,Continuous (fun p=>L p i)) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    CavityJointSpatialTwoJets (fun z : P×FiniteStateField S=>
      Real.log (cavityOuterPosteriorNormalizer V a (L z.1) s N R z.2)) :=by
  let F:=fun z : P×FiniteStateField S=>Real.log (cavityOuterPosteriorNormalizer V a (L z.1) s N R z.2)
  have hs(p):ContDiff ℝ ∞ (fun H=>F (p,H)):=contDiff_log_cavityOuterPosteriorNormalizer V a ha (L p) s N R
  have hc:Continuous F:=continuous_cavityOuterPosteriorLogNormalizer_input_family V a ha L hL s N R
  obtain ⟨B2,hB2,hb2⟩:=cavityOuterPosteriorLogNormalizer_uniform_positive_jets (n:=n) (J:=J) V a ha ha1 hdec s N 2
  obtain ⟨B3,hB3,hb3⟩:=cavityOuterPosteriorLogNormalizer_uniform_positive_jets (n:=n) (J:=J) V a ha ha1 hdec s N 3
  have hfirst : Continuous (fun z : P×FiniteStateField S=>fderiv ℝ (fun H=>F (z.1,H)) z.2):=
    continuous_fderiv_family_of_uniform_secondJet F hc hs (B2^2)
      (pow_nonneg (zero_le_one.trans hB2) _) (fun p H=>hb2 (L p) R 2 (by omega) le_rfl H)
  refine ⟨hs,hc,hfirst,?_⟩
  exact continuous_fderiv_family_of_uniform_secondJet _ hfirst
    (fun p=>(hs p).fderiv_right (by simp)) (B3^3) (pow_nonneg (zero_le_one.trans hB3) _)
    (fun p H=>by
      change ‖iteratedFDeriv ℝ 2 (fderiv ℝ (fun y=>F (p,y))) H‖≤B3^3
      rw [norm_iteratedFDeriv_fderiv]
      exact hb3 (L p) R 3 (by omega) le_rfl H)

theorem cavityOuterPosteriorNormalizer_jointSpatial_input_family
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀i,Continuous (fun p=>L p i)) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    CavityJointSpatialTwoJets (fun z : P×FiniteStateField S=>
      cavityOuterPosteriorNormalizer V a (L z.1) s N R z.2) :=by
  have hh:=(cavityOuterPosteriorLogNormalizer_jointSpatial_input_family V a ha ha1 hdec L hL s N R).exp
  have he : (fun z : P×FiniteStateField S=>
      Real.exp (Real.log (cavityOuterPosteriorNormalizer V a (L z.1) s N R z.2)))=
      (fun z : P×FiniteStateField S=>cavityOuterPosteriorNormalizer V a (L z.1) s N R z.2) :=by
    funext z
    exact Real.exp_log (finiteCascadeTreeGaussianNormalizer_pos V a ha (L z.1) s N R z.2)
  change CavityJointSpatialTwoJets (fun z : P×FiniteStateField S=>
    Real.exp (Real.log (cavityOuterPosteriorNormalizer V a (L z.1) s N R z.2))) at hh
  rw [he] at hh
  exact hh

theorem cavityOuterPosteriorMean_jointSpatial_input_family
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀i,Continuous (fun p=>L p i)) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : P×FiniteStateField S→ℝ) (hf : Continuous f)
    (hsf : ∀p,BoundedJets (fun H=>f (p,H)))
    (W : P→(Fin N→Field n)→L[ℝ]FiniteStateField S) (hW : Continuous W)
    (G : ℕ→ℝ) (hG : ∀r,0≤G r)
    (hb : ∀p r H,‖iteratedFDeriv ℝ r (fun Q=>f (p,Q)) H‖≤G r) :
    CavityJointSpatialTwoJets (fun z : P×FiniteStateField S=>
      cavityOuterPosteriorMean V a (L z.1) s N R (fun H=>f (z.1,H)) (W z.1) z.2) :=by
  let F:=fun z : P×FiniteStateField S=>cavityOuterPosteriorMean V a (L z.1) s N R (fun H=>f (z.1,H)) (W z.1) z.2
  have hs(p):ContDiff ℝ ∞ (fun H=>F (p,H)):=
    contDiff_cavityOuterPosteriorMean V a ha ha1 hdec (L p) s N R _ (hsf p) (W p)
  have hc:Continuous F:=continuous_cavityOuterPosteriorMean_input_family V a ha L hL s N R f hf W hW (G 0) (hG 0)
    (fun p H=>by simpa only [norm_iteratedFDeriv_zero] using hb p 0 H)
  obtain ⟨B2,hB2,hb2⟩:=cavityOuterPosteriorMean_uniform_jet_bound (n:=n) (J:=J) V a ha ha1 hdec s N 2 G hG
  obtain ⟨B3,hB3,hb3⟩:=cavityOuterPosteriorMean_uniform_jet_bound (n:=n) (J:=J) V a ha ha1 hdec s N 3 G hG
  have hfirst : Continuous (fun z : P×FiniteStateField S=>fderiv ℝ (fun H=>F (z.1,H)) z.2):=
    continuous_fderiv_family_of_uniform_secondJet F hc hs B2 hB2
      (fun p H=>hb2 (L p) R _ (hsf p) (W p) (fun i _ Q=>hb p i Q) H)
  refine ⟨hs,hc,hfirst,?_⟩
  exact continuous_fderiv_family_of_uniform_secondJet _ hfirst
    (fun p=>(hs p).fderiv_right (by simp)) B3 hB3
    (fun p H=>by
      change ‖iteratedFDeriv ℝ 2 (fderiv ℝ (fun y=>F (p,y))) H‖≤B3
      rw [norm_iteratedFDeriv_fderiv]
      exact hb3 (L p) R _ (hsf p) (W p) (fun i _ Q=>hb p i Q) H)

theorem cavityOuterPosteriorWeightedMean_jointSpatial_input_family
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀i,Continuous (fun p=>L p i)) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : P×FiniteStateField S→ℝ) (hf : Continuous f)
    (hsf : ∀p,BoundedJets (fun H=>f (p,H)))
    (W : P→(Fin N→Field n)→L[ℝ]FiniteStateField S) (hW : Continuous W)
    (G : ℕ→ℝ) (hG : ∀r,0≤G r)
    (hb : ∀p r H,‖iteratedFDeriv ℝ r (fun Q=>f (p,Q)) H‖≤G r) :
    CavityJointSpatialTwoJets (fun z : P×FiniteStateField S=>
      cavityOuterPosteriorWeightedMean V a (L z.1) s N R (fun H=>f (z.1,H)) (W z.1) z.2) :=by
  have hh:=(cavityOuterPosteriorNormalizer_jointSpatial_input_family V a ha ha1 hdec L hL s N R).mul
    (cavityOuterPosteriorMean_jointSpatial_input_family V a ha ha1 hdec L hL s N R f hf hsf W hW G hG hb)
  convert hh using 1
  funext z
  exact cavityOuterPosteriorWeightedMean_eq_normalizer_mul V a ha (L z.1) s N R _ (hsf z.1) (W z.1) z.2

end QuantitativeFollowup
