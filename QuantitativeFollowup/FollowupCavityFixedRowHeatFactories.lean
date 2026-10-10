module
public import QuantitativeFollowup.FollowupCavityFixedRowExpectations
public import QuantitativeFollowup.FollowupCavityMixtureJetData
public import QuantitativeFollowup.FixedRowSymmetryPosteriorTransportOuter
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterMean

@[expose] public section

/-! The genuine retained-line pushlaw supplies actual fixed-row smoothness
and exponential growth. Both the root tilt and every retained field remain
in the observable; no differentiability or mixture identity is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityFixedRowFieldMean (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (d : ℕ) (f : FiniteStateField (Configuration (n+1))→ℝ) (theta : Field n) : ℝ :=
  ∫z,f (cavityFixedRowLineField (k+2) d z.1 z.2) ∂cavityFixedRowLaw D s a theta

theorem cavityFixedRowFieldMean_eq_outer (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (d : ℕ) (hd : d ≤ k+2) (f : FiniteStateField (Configuration (n+1))→ℝ)
    (hf : Measurable f) :
    cavityFixedRowFieldMean D s a d f = fun theta=>
      cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) f
        (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d)
        (cavityFixedRowOffset n theta) := by
  funext theta
  exact (cavityOuterPosteriorMean_eq_lineField_integral _ _ (anisotropicSchemeMass_nonneg s)
    _ a (k+2) d hd _ f hf _).symm

theorem contDiff_cavityFixedRowFieldMean (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (d : ℕ) (hd : d ≤ k+2) (f : FiniteStateField (Configuration (n+1))→ℝ)
    (hf : BoundedJets f) : ContDiff ℝ ∞ (cavityFixedRowFieldMean D s a d f) := by
  rw [cavityFixedRowFieldMean_eq_outer D s a d hd f hf.1.continuous.measurable]
  exact (contDiff_cavityOuterPosteriorMean _ _ (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_le_one s 0)
    (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step s)) _ a (k+2) _ f hf _).comp
      (cavityFixedRowOffset n).contDiff

theorem cavityFixedRowFieldMean_weighted_eq_outer (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (d : ℕ) (hd : d ≤ k+2) (f : FiniteStateField (Configuration (n+1))→ℝ)
    (hf : BoundedJets f) :
    (fun theta=>cavityFixedRowNormalizer D s a theta*cavityFixedRowFieldMean D s a d f theta)=
      fun theta=>cavityOuterPosteriorWeightedMean (fun _ : Configuration (n+1)=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) f
        (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d)
        (cavityFixedRowOffset n theta) := by
  rw [cavityFixedRowFieldMean_eq_outer D s a d hd f hf.1.continuous.measurable]
  funext theta
  exact (cavityOuterPosteriorWeightedMean_eq_normalizer_mul _ _ (anisotropicSchemeMass_nonneg s)
    _ a (k+2) _ f hf _ _).symm

theorem cavityFixedRowNormalizer_heat_data (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) : Nonempty (CavityRowHeatData (cavityFixedRowNormalizer D s a)) := by
  exact cavityRowHeatData_of_exponentialSmooth_compCLM _
    (exponentialSmoothOn_cavityOuterPosteriorNormalizer _ _ (anisotropicSchemeMass_nonneg s)
      (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D))
    (cavityFixedRowOffset n)

theorem cavityFixedRowFieldMean_weighted_heat_data (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d ≤ k+2)
    (f : FiniteStateField (Configuration (n+1))→ℝ) (hf : BoundedJets f) :
    Nonempty (CavityRowHeatData (fun theta=>
      cavityFixedRowNormalizer D s a theta*cavityFixedRowFieldMean D s a d f theta)) := by
  rw [cavityFixedRowFieldMean_weighted_eq_outer D s a d hd f hf]
  exact cavityRowHeatData_of_exponentialSmooth_compCLM _
    (exponentialSmoothOn_cavityOuterPosteriorWeightedMean _ _ (anisotropicSchemeMass_nonneg s)
      (anisotropicSchemeMass_le_one s 0)
      (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step s)) _ a (k+2) _ f hf _)
    (cavityFixedRowOffset n)

theorem contDiff_cavityFixedRowLastMean (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d ≤ k+2) :
    ContDiff ℝ ∞ (cavityFixedRowLastMean D s a d) :=
  contDiff_cavityFixedRowFieldMean D s a d hd _ (boundedJets_cavityFixedRowLastFieldSquare D s d)

theorem contDiff_cavityFixedRowRestMean (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d ≤ k+2) :
    ContDiff ℝ ∞ (cavityFixedRowRestMean D s a d) :=
  contDiff_cavityFixedRowFieldMean D s a d hd _ (boundedJets_cavityFixedRowRestFieldSquare D s d)

theorem contDiff_cavityFixedRowProductMean (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d ≤ k+2) :
    ContDiff ℝ ∞ (cavityFixedRowProductMean D s a d) :=
  contDiff_cavityFixedRowFieldMean D s a d hd _ (boundedJets_cavityFixedRowProductFieldSquare D s d)

theorem cavityFixedRowLastMean_weighted_heat_data (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d ≤ k+2) :
    Nonempty (CavityRowHeatData (fun theta=>
      cavityFixedRowNormalizer D s a theta*cavityFixedRowLastMean D s a d theta)) :=
  cavityFixedRowFieldMean_weighted_heat_data D s a d hd _ (boundedJets_cavityFixedRowLastFieldSquare D s d)

theorem cavityFixedRowRestMean_weighted_heat_data (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d ≤ k+2) :
    Nonempty (CavityRowHeatData (fun theta=>
      cavityFixedRowNormalizer D s a theta*cavityFixedRowRestMean D s a d theta)) :=
  cavityFixedRowFieldMean_weighted_heat_data D s a d hd _ (boundedJets_cavityFixedRowRestFieldSquare D s d)

theorem cavityFixedRowProductMean_weighted_heat_data (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d ≤ k+2) :
    Nonempty (CavityRowHeatData (fun theta=>
      cavityFixedRowNormalizer D s a theta*cavityFixedRowProductMean D s a d theta)) :=
  cavityFixedRowFieldMean_weighted_heat_data D s a d hd _ (boundedJets_cavityFixedRowProductFieldSquare D s d)

end QuantitativeFollowup
