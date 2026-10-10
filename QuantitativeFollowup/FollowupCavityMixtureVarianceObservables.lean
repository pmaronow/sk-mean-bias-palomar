module
public import QuantitativeFollowup.FollowupCavityMixtureRestObservableJets
public import QuantitativeFollowup.FollowupCavityMixtureVarianceInput
public import QuantitativeFollowup.FollowupCavityRootCharges

@[expose] public section

/-! The exact fixed-row retained tests have common jets under arbitrary
positive last variances, with the rest model fixed. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper SpinGlass.Targets
open scoped ContDiff Topology BigOperators
namespace QuantitativeFollowup
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityFixedRowLastFeature (n : ℕ) : FiniteStateField (Configuration (n+1)) :=
  WithLp.toLp 2 (fun sigma=>Paper.spinSign (sigma (Fin.last n)))
def cavityFixedRowRestFeature (n : ℕ) (i : Fin n) : FiniteStateField (Configuration (n+1)) :=
  WithLp.toLp 2 (fun sigma=>Paper.spinSign (sigma i.castSucc))
def cavityFixedRowLastCommonJetBound (n r : ℕ) : ℝ :=
  cavityProductJetBound (cavityMeanFeatureJetBound (Configuration (n+1)) (n+1) (cavityFixedRowLastFeature n))
    (cavityMeanFeatureJetBound (Configuration (n+1)) (n+1) (cavityFixedRowLastFeature n)) r
def cavityFixedRowRestCommonJetBound (n r : ℕ) : ℝ :=
  cavityRestFeatureJetBound (Configuration (n+1)) (n+1) (cavityFixedRowRestFeature n) r

theorem cavityFixedRowLastCommonJetBound_nonneg (n r : ℕ) : 0≤cavityFixedRowLastCommonJetBound n r :=
  cavityProductJetBound_nonneg _ _ (cavityMeanFeatureJetBound_nonneg _) (cavityMeanFeatureJetBound_nonneg _) r

theorem cavityFixedRowRestCommonJetBound_nonneg (n r : ℕ) : 0≤cavityFixedRowRestCommonJetBound n r :=
  cavityRestFeatureJetBound_nonneg _ r

theorem norm_cavityFixedRowLastFieldSquare_jet_uniform (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d r : ℕ) (H : FiniteStateField (Configuration (n+1))) :
    ‖iteratedFDeriv ℝ r (cavityFixedRowLastFieldSquare D s d) H‖≤cavityFixedRowLastCommonJetBound n r :=
  norm_cavityFiniteEnergyFeatureSquare_jet_uniform _ _ (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_le_one s 0) (anisotropicSchemeMass_antitone s) _ d _ r H

theorem norm_cavityFixedRowRestFieldSquare_jet_uniform (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d r : ℕ) (H : FiniteStateField (Configuration (n+1))) :
    ‖iteratedFDeriv ℝ r (cavityFixedRowRestFieldSquare D s d) H‖≤cavityFixedRowRestCommonJetBound n r :=
  norm_cavityFiniteEnergyRestOverlap_jet_uniform _ _ (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_le_one s 0) (anisotropicSchemeMass_antitone s) _ d _ r H

theorem norm_cavityFixedRowProductFieldSquare_jet_uniform (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d r : ℕ) (H : FiniteStateField (Configuration (n+1))) :
    ‖iteratedFDeriv ℝ r (fun Q=>cavityFixedRowLastFieldSquare D s d Q*cavityFixedRowRestFieldSquare D s d Q) H‖≤
      cavityProductJetBound (cavityFixedRowLastCommonJetBound n) (cavityFixedRowRestCommonJetBound n) r :=
  norm_cavityProduct_jet_uniform _ _ (boundedJets_cavityFixedRowLastFieldSquare D s d).1
    (boundedJets_cavityFixedRowRestFieldSquare D s d).1 _ _
    (cavityFixedRowLastCommonJetBound_nonneg n) (cavityFixedRowRestCommonJetBound_nonneg n)
    (norm_cavityFixedRowLastFieldSquare_jet_uniform D s d) (norm_cavityFixedRowRestFieldSquare_jet_uniform D s d) r H

theorem continuous_cavityFixedRowLastFieldSquare_positive_variance_band
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (d : ℕ) (l r : ℝ) (hl : 0<l) :
    Continuous (fun z:Icc l r×FiniteStateField (Configuration (n+1))=>
      cavityFixedRowLastFieldSquare (anisotropicReplaceVariance D (Fin.last n) z.1) s d z.2) :=by
  exact (continuous_cavityFiniteEnergyFeatureMean_input_family (fun _=>0) (anisotropicSchemeMass s)
    (anisotropicSchemeMass_nonneg s) (anisotropicSchemeMass_le_one s 0) (anisotropicSchemeMass_antitone s)
    (fun b:Icc l r=>cavityFiniteEnergyInput (anisotropicReplaceVariance D (Fin.last n) b) s)
    (continuous_cavityFiniteEnergyInput_positive_variance_band D (Fin.last n) s l r hl) d
    (cavityFixedRowLastFeature n)).pow 2

theorem continuous_cavityFixedRowRestFieldSquare_positive_variance_band
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (d : ℕ) (l r : ℝ) (hl : 0<l) :
    Continuous (fun z:Icc l r×FiniteStateField (Configuration (n+1))=>
      cavityFixedRowRestFieldSquare (anisotropicReplaceVariance D (Fin.last n) z.1) s d z.2) :=
  continuous_cavityFiniteEnergyRestOverlap_input_family (fun _=>0) (anisotropicSchemeMass s)
    (anisotropicSchemeMass_nonneg s) (anisotropicSchemeMass_le_one s 0) (anisotropicSchemeMass_antitone s)
    (fun b:Icc l r=>cavityFiniteEnergyInput (anisotropicReplaceVariance D (Fin.last n) b) s)
    (continuous_cavityFiniteEnergyInput_positive_variance_band D (Fin.last n) s l r hl) d
    (cavityFixedRowRestFeature n)

end QuantitativeFollowup
