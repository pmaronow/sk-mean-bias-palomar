module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeChargeFeatures
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeCenterMeans

@[expose] public section

/-! Native charge parameters and actual centering constants used in the
pointwise response. This leaf contains definitions only. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false

abbrev cavityNativeResponseChargeDepth (k : ℕ) (r : Option (Option (Fin (k+1)))) : ℕ :=
  k+2-cavityOuterChargePosition (k+1) r

abbrev cavityNativeResponseChargeParameter (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (sample : AnisotropicDisorderBrownianSample (n+1))
    (r : Option (Option (Fin (k+1)))) : AnisotropicParameter (n+1) :=
  anisotropicProcessParameter D (Paper.parisiSchemeMeasure s) (cavityOuterSchemeChargeNode s r) sample

abbrev cavityNativeResponseLastCentered (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (P : AnisotropicParameter (n+1)) : ℝ :=
  cavityFixedRowLastFieldSquare D s d (anisotropicEnergyMap D P)-
    cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D)
      (cavityFixedRowLastFieldSquare D s d)
      (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d) 0

abbrev cavityNativeResponseRestCentered (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (P : AnisotropicParameter (n+1)) : ℝ :=
  cavityFixedRowRestFieldSquare D s d (anisotropicEnergyMap D P)-
    cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D)
      (cavityFixedRowRestFieldSquare D s d)
      (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d) 0

end QuantitativeFollowup
