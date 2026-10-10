module
public import QuantitativeFollowup.AnisotropicFiniteMeasureAgreement
public import QuantitativeFollowup.AnisotropicVarianceNoiseRestart
public import QuantitativeFollowup.AnisotropicSpinResponses

@[expose] public section

/-! The actual arbitrary-profile Picard diffusion for a finite scheme
coincides pathwise with that scheme's genuine finite diffusion. Exact
potential agreement identifies the drift before any stochastic law is used. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem anisotropicWhitenedDrift_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) :
    anisotropicWhitenedDrift D (Paper.parisiSchemeMeasure s) g=
      anisotropicWhitenedFiniteDrift D s g := by
  funext r p y
  unfold anisotropicWhitenedDrift anisotropicWhitenedFiniteDrift
  rw [anisotropicMeasureTailMagnetization_scheme_eq_finite]

theorem anisotropicWhitenedDriftData_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) :
    anisotropicWhitenedDriftData D (Paper.parisiSchemeMeasure s) g=
      anisotropicWhitenedFiniteDriftData D s g := by
  unfold anisotropicWhitenedDriftData anisotropicWhitenedFiniteDriftData
  congr 1
  exact anisotropicWhitenedDrift_scheme_eq_finite D s g

theorem anisotropicRestartState_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    anisotropicRestartState D (Paper.parisiSchemeMeasure s) g q x=
      anisotropicFiniteRestartState D s g q x := by
  unfold anisotropicRestartState anisotropicFiniteRestartState
    anisotropicRestartDriftData anisotropicFiniteRestartDriftData
  rw [anisotropicWhitenedDriftData_scheme_eq_finite]

theorem anisotropicMeasureState_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n) :
    anisotropicMeasureState D (Paper.parisiSchemeMeasure s) q p=
      anisotropicFiniteWienerState D s (q:ℝ).toNNReal p := by
  have hq1 : (q:ℝ).toNNReal≤1 := by simpa using Real.toNNReal_le_toNNReal q.property.2
  have hh:=anisotropicWhitenedState_eq_vectorAdditiveState D (Paper.parisiSchemeMeasure s) p.1
    (((0,0),p.2):VectorDisorderBrownianSample n) (q:ℝ).toNNReal hq1
  rw [Real.coe_toNNReal _ q.property.1,anisotropicWhitenedDriftData_scheme_eq_finite] at hh
  have he:=congrArg (anisotropicNoiseMap D) hh
  simpa only [anisotropicWhitenedState,anisotropicNoiseMap_inverseNoise,
    anisotropicFiniteWienerState,anisotropicWhitenedFiniteState] using he

theorem anisotropicProcessParameter_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n) :
    anisotropicProcessParameter D (Paper.parisiSchemeMeasure s) q p=
      anisotropicFiniteProcessParameter D s q p := by
  unfold anisotropicProcessParameter anisotropicFiniteProcessParameter
  rw [anisotropicMeasureState_scheme_eq_finite]

theorem anisotropicProcessSpinResponse_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (i : Fin n) (p : AnisotropicDisorderBrownianSample n) :
    anisotropicProcessSpinResponse D (Paper.parisiSchemeMeasure s) q i p=
      anisotropicFiniteProcessMagnetization D s q p i := by
  unfold anisotropicProcessSpinResponse anisotropicProcessMagnetization
    anisotropicFiniteProcessMagnetization
  rw [anisotropicMeasureTailMagnetization_scheme_eq_finite,
    anisotropicProcessParameter_scheme_eq_finite]

theorem anisotropicTailPairResponse_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : AnisotropicCouplingIndex n) :
    anisotropicTailPairResponse D (Paper.parisiSchemeMeasure s) q P e=
      anisotropicFiniteTailPairResponse D s q P e := by
  unfold anisotropicTailPairResponse anisotropicFiniteTailPairResponse
  rw [anisotropicMeasureTailDifferential_scheme_eq_finite]

theorem anisotropicProcessPairResponse_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n)
    (p : AnisotropicDisorderBrownianSample n) :
    anisotropicProcessPairResponse D (Paper.parisiSchemeMeasure s) q e p=
      anisotropicFiniteTailPairResponse D s q (anisotropicFiniteProcessParameter D s q p) e := by
  unfold anisotropicProcessPairResponse
  rw [anisotropicTailPairResponse_scheme_eq_finite,anisotropicProcessParameter_scheme_eq_finite]

theorem anisotropicMeasureSampleLaw_scheme_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) :
    anisotropicMeasureSampleLaw D (Paper.parisiSchemeMeasure s) a=
      (anisotropicFiniteOuterLaw D s a).prod (vectorBrownianMeasure n) := by
  unfold anisotropicMeasureSampleLaw
  rw [anisotropicMeasureOuterLaw_scheme_eq_finite]

end QuantitativeFollowup
