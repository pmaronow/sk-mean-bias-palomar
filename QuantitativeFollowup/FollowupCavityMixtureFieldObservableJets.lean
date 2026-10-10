module
public import QuantitativeFollowup.FollowupCavityMixtureInputContinuity
public import QuantitativeFollowup.FollowupCavityFixedRowObservableBounds

@[expose] public section

/-! Genuine common bounds for all jets of the retained spin-square tests.
The constants are independent of the Gaussian input maps. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped ContDiff BigOperators
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityMeanFeatureJetBound (S : Type) [Fintype S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (n : ℕ) (b : FiniteStateField S) (r : ℕ) : ℝ :=
  ‖b‖*finiteStateSpatialJetBound S n (r+1)

def cavityProductJetBound (B C : ℕ→ℝ) (r : ℕ) : ℝ :=
  ∑i∈Finset.range (r+1),(r.choose i:ℝ)*B i*C (r-i)

theorem cavityProductJetBound_nonneg (B C : ℕ→ℝ) (hB : ∀r,0≤B r)
    (hC : ∀r,0≤C r) (r : ℕ) : 0≤cavityProductJetBound B C r :=
  Finset.sum_nonneg fun i _=>mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB _)) (hC _)

theorem norm_cavityFiniteEnergyFeatureMean_jet_uniform (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (d : ℕ) (b : FiniteStateField S)
    (r : ℕ) (H : FiniteStateField S) :
    ‖iteratedFDeriv ℝ r (cavityFiniteEnergyFeatureMean V a L d b) H‖≤
      cavityMeanFeatureJetBound S n b r :=by
  have hs:ContDiff ℝ ∞ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L d)):=
    (contDiff_finiteStateGaussianTerminalCascade V a ha L d).fderiv_right (by simp)
  apply (norm_iteratedFDeriv_clm_apply_const hs.contDiffAt (by simp)).trans
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_left
    (norm_finiteStateCascade_jet_le_uniform V a ha ha1 hdec L d (r+1) (by omega) H) (norm_nonneg b)

theorem norm_cavityProduct_jet_uniform {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E→ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (B C : ℕ→ℝ) (hB : ∀r,0≤B r) (hC : ∀r,0≤C r)
    (hfb : ∀r H,‖iteratedFDeriv ℝ r f H‖≤B r)
    (hgb : ∀r H,‖iteratedFDeriv ℝ r g H‖≤C r) (r : ℕ) (H : E) :
    ‖iteratedFDeriv ℝ r (fun x=>f x*g x) H‖≤cavityProductJetBound B C r :=by
  apply (norm_iteratedFDeriv_mul_le hf hg H (by simp)).trans
  exact Finset.sum_le_sum fun i _=>by
    have hb:=mul_le_mul (hfb i H) (hgb (r-i) H) (norm_nonneg _) (hB i)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (r.choose i))

theorem norm_cavityFiniteEnergyFeatureSquare_jet_uniform (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (d : ℕ) (b : FiniteStateField S)
    (r : ℕ) (H : FiniteStateField S) :
    ‖iteratedFDeriv ℝ r (fun Q=>(cavityFiniteEnergyFeatureMean V a L d b Q)^2) H‖≤
      cavityProductJetBound (cavityMeanFeatureJetBound S n b) (cavityMeanFeatureJetBound S n b) r :=by
  have hn(i):0≤cavityMeanFeatureJetBound S n b i:=
    mul_nonneg (norm_nonneg _) (finiteStateSpatialJetBound_nonneg S n _)
  simpa only [pow_two] using norm_cavityProduct_jet_uniform _ _
    (boundedJets_cavityFiniteEnergyFeatureMean V a ha L d b).1
    (boundedJets_cavityFiniteEnergyFeatureMean V a ha L d b).1 _ _ hn hn
    (norm_cavityFiniteEnergyFeatureMean_jet_uniform V a ha ha1 hdec L d b)
    (norm_cavityFiniteEnergyFeatureMean_jet_uniform V a ha ha1 hdec L d b) r H

theorem continuous_cavityFiniteEnergyFeatureMean_input_family
    {P : Type} [TopologicalSpace P] [FirstCountableTopology P]
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀i,Continuous (fun p=>L p i)) (d : ℕ) (b : FiniteStateField S) :
    Continuous (fun z : P×FiniteStateField S=>cavityFiniteEnergyFeatureMean V a (L z.1) d b z.2) :=
  (continuous_cavityCascade_input_fderiv V a ha ha1 hdec L hL d).clm_apply continuous_const

end QuantitativeFollowup
