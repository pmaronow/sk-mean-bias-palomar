module
public import QuantitativeFollowup.AnisotropicFiniteMeshGrouping
public import QuantitativeFollowup.AnisotropicMeasureOuterLaw
public import QuantitativeFollowup.FollowupCavityRootNormalizerFiniteAgreement
public import QuantitativePaper.VectorMeasureEndpoints

@[expose] public section

/-! Exact arbitrary-scheme agreement with the actual arbitrary-profile
anisotropic potential and outer law. Uniform cells group by the original
finite masses, and their rounded original nodes converge by genuine Gaussian
integral continuity. No finite-agreement hypothesis is supplied. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem anisotropicMeasureTailPotential_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    anisotropicMeasureTailPotential D (Paper.parisiSchemeMeasure s) q P=
      anisotropicTailRecursion D s q (k+2) P := by
  apply tendsto_nhds_unique (tendsto_anisotropicDyadicTailPotential D (Paper.parisiSchemeMeasure s) q P)
  have hh:=(tendsto_anisotropicRoundedMeshTailRecursion D s q P (j:=k+2) le_rfl).comp
    tendsto_vectorDyadicIndex
  convert hh using 1
  funext j
  dsimp only [Function.comp_def]
  rw [anisotropicDyadicTailPotential,anisotropicTailRecursion_grid_eq_uniform,
    anisotropicRoundedMeshTailRecursion_full_eq_uniform]

theorem anisotropicMeasurePotential_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (P : AnisotropicParameter n) :
    anisotropicMeasurePotential D (Paper.parisiSchemeMeasure s) P=
      anisotropicFinitePotential D s (k+2) P := by
  rw [←anisotropicMeasureTailPotential_zero,anisotropicMeasureTailPotential_scheme_eq_finite,
    anisotropicTailRecursion_zero D s le_rfl]

theorem anisotropicMeasureTailDifferential_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    fderiv ℝ (anisotropicMeasureTailPotential D (Paper.parisiSchemeMeasure s) q) P=
      fderiv ℝ (anisotropicFiniteTailPotential D s q) P := by
  have he : anisotropicMeasureTailPotential D (Paper.parisiSchemeMeasure s) q=
      anisotropicFiniteTailPotential D s q := funext fun Q=>
    anisotropicMeasureTailPotential_scheme_eq_finite D s q Q
  rw [he]

theorem anisotropicMeasureTailMagnetization_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    anisotropicMeasureTailMagnetization D (Paper.parisiSchemeMeasure s) q P=
      anisotropicFiniteTailMagnetization D s q P := by
  unfold anisotropicMeasureTailMagnetization anisotropicFiniteTailMagnetization
  rw [anisotropicMeasureTailDifferential_scheme_eq_finite]

theorem anisotropicMeasureOuterPartition_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) :
    anisotropicMeasureOuterPartition D (Paper.parisiSchemeMeasure s) a=
      anisotropicFiniteOuterPartition D s a := by
  unfold anisotropicMeasureOuterPartition anisotropicFiniteOuterPartition
  simp_rw [anisotropicMeasurePotential_scheme_eq_finite]
  rfl

theorem anisotropicMeasureOuterLaw_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) :
    anisotropicMeasureOuterLaw D (Paper.parisiSchemeMeasure s) a=
      anisotropicFiniteOuterLaw D s a := by
  unfold anisotropicMeasureOuterLaw anisotropicFiniteOuterLaw
  simp_rw [anisotropicMeasurePotential_scheme_eq_finite]
  rfl

theorem anisotropicMeasureOuterPartition_scheme_eq_cavityPathNormalizer
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n) :
    anisotropicMeasureOuterPartition D (Paper.parisiSchemeMeasure s) a=
      cavityPathNormalizer D s a i (k+2) (D.variance i) := by
  rw [anisotropicMeasureOuterPartition_scheme_eq_finite]
  exact anisotropicFiniteOuterPartition_eq_cavityPathNormalizer D s a i

end QuantitativeFollowup
