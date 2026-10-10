module
public import QuantitativeFollowup.FollowupCavityMixtureFieldObservableJets

@[expose] public section

/-! Map-independent spatial bounds and input continuity for the actual
selected-rest mean-square and its last-spin-square product. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped ContDiff BigOperators
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityRestFeatureJetBound {ι : Type} [Fintype ι]
    (S : Type) [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (n : ℕ) (b : ι→FiniteStateField S) (r : ℕ) : ℝ :=
  (Fintype.card ι:ℝ)⁻¹*∑i,cavityProductJetBound
    (cavityMeanFeatureJetBound S n (b i)) (cavityMeanFeatureJetBound S n (b i)) r

theorem cavityMeanFeatureJetBound_nonneg (b : FiniteStateField S) (r : ℕ) :
    0≤cavityMeanFeatureJetBound S n b r :=
  mul_nonneg (norm_nonneg _) (finiteStateSpatialJetBound_nonneg S n _)

theorem cavityRestFeatureJetBound_nonneg {ι : Type} [Fintype ι]
    (b : ι→FiniteStateField S) (r : ℕ) : 0≤cavityRestFeatureJetBound S n b r :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun i _=>
    cavityProductJetBound_nonneg _ _ (cavityMeanFeatureJetBound_nonneg _) (cavityMeanFeatureJetBound_nonneg _) r)

theorem norm_cavityFiniteEnergyRestOverlap_jet_uniform {ι : Type} [Fintype ι]
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (d : ℕ) (b : ι→FiniteStateField S)
    (r : ℕ) (H : FiniteStateField S) :
    ‖iteratedFDeriv ℝ r (cavityFiniteEnergyRestOverlap V a L d b) H‖≤
      cavityRestFeatureJetBound S n b r :=by
  classical
  have hs(i):ContDiff ℝ ∞ (fun Q=>(cavityFiniteEnergyFeatureMean V a L d (b i) Q)^2):=
    (boundedJets_cavityFiniteEnergyFeatureMean V a ha L d (b i)).1.pow 2
  have hsum:ContDiff ℝ ∞ (fun Q=>∑i,(cavityFiniteEnergyFeatureMean V a L d (b i) Q)^2):=
    ContDiff.sum fun i _=>hs i
  unfold cavityFiniteEnergyRestOverlap
  change ‖iteratedFDeriv ℝ r (fun Q=>(Fintype.card ι:ℝ)⁻¹ •
    (∑i,(cavityFiniteEnergyFeatureMean V a L d (b i) Q)^2)) H‖≤_
  rw [iteratedFDeriv_const_smul_apply' (i:=r) (hsum.of_le (by simp)).contDiffAt,
    norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)),
    iteratedFDeriv_fun_sum_apply (fun i _=>(hs i).of_le (by simp) |>.contDiffAt)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>
    norm_cavityFiniteEnergyFeatureSquare_jet_uniform V a ha ha1 hdec L d (b i) r H)

theorem continuous_cavityFiniteEnergyRestOverlap_input_family
    {P ι : Type} [Fintype ι] [TopologicalSpace P] [FirstCountableTopology P]
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀i,Continuous (fun p=>L p i)) (d : ℕ) (b : ι→FiniteStateField S) :
    Continuous (fun z : P×FiniteStateField S=>cavityFiniteEnergyRestOverlap V a (L z.1) d b z.2) :=by
  unfold cavityFiniteEnergyRestOverlap
  exact continuous_const.mul (continuous_finset_sum _ fun i _=>
    (continuous_cavityFiniteEnergyFeatureMean_input_family V a ha ha1 hdec L hL d (b i)).pow 2)

end QuantitativeFollowup
