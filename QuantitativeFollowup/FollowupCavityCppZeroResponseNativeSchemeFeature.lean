module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeHistoryMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastSquareRowJets
public import QuantitativeFollowup.AnisotropicBinaryFeatureStieltjes
public import QuantitativeFollowup.AnisotropicBinaryFeatureLimits
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVarianceFieldFeatures

@[expose] public section

/-! Every retained energy-feature derivative is the actual native feature
response at that original scheme node. Zero and repeated cells are retained
through the exact finite tail-potential identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFiniteEnergyPairMean_at_native_scheme_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i≤k+2) (e : AnisotropicCouplingIndex n)
    (sample : AnisotropicDisorderBrownianSample n) :
    cavityFiniteEnergyFeatureMean (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) (k+2-i) (anisotropicPairFeature e)
      (anisotropicEnergyMap D (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s i hi) sample))=
      anisotropicProcessPairResponse D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s i hi) e sample :=by
  rw [cavityFiniteEnergyFeatureMean_at_parameter,
    anisotropicProcessPairResponse_scheme_eq_finite,
    anisotropicFiniteTailPairResponse_eq_feature_node,
    anisotropicProcessParameter_scheme_eq_finite]

theorem cavityFiniteEnergyRowSecond_at_native_scheme_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i≤k+2) (e : AnisotropicCouplingIndex n)
    (sample : AnisotropicDisorderBrownianSample n) :
    cavityFiniteEnergyRowSecond (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) (k+2-i) (anisotropicPairFeature e)
      (anisotropicEnergyMap D (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s i hi) sample))=
      anisotropicProcessPairSecond D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s i hi) e sample :=by
  rw [cavityFiniteEnergyRowSecond_at_parameter]
  unfold anisotropicProcessPairSecond anisotropicTailPairSecond
  have he:anisotropicMeasureTailPotential (anisotropicUnitCouplings D) (Paper.parisiSchemeMeasure s)
      (anisotropicSchemeNode s i hi)=
      anisotropicFiniteTailPotential (anisotropicUnitCouplings D) s (anisotropicSchemeNode s i hi):=
    funext fun Q=>anisotropicMeasureTailPotential_scheme_eq_finite _ s _ Q
  rw [he]
  exact (anisotropicFiniteTailPairSecond_node D s i hi _ e).symm

end QuantitativeFollowup
