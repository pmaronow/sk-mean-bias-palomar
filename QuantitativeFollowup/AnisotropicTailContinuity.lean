module
public import QuantitativeFollowup.AnisotropicTailHessian
public import QuantitativeFollowup.AnisotropicFiniteTailResponse
public import FourPapersCommon.GenericFiniteStateCascadeEndpointContinuity
public import FourPapersCommon.JointDerivativeContinuity

@[expose] public section

/-! Actual restarted anisotropic potentials, gradients and Hessians are
jointly continuous through physical overlap atoms and zero-variance cells.
The arbitrary-profile objects inherit continuity from uniform approximation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

theorem anisotropicGaussianShift_eq_finiteStateStep
    (A : Field n →L[ℝ] AnisotropicParameter n) (a : ℝ)
    (F : AnisotropicParameter n → ℝ) (P : AnisotropicParameter n) :
    gaussianShiftColeHopf A a F P=finiteStateGaussianStep a A F P := by
  unfold gaussianShiftColeHopf gaussianShiftAverage gaussianShiftPartition
    finiteStateGaussianStep OverlapPaper.sourceLogAverage
  rw [fieldGaussian_eq_stdGaussian]

theorem continuous_anisotropicTailRecursion_joint (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (hj : j ≤ k+2) :
    Continuous (fun z : Paper.Overlap×AnisotropicParameter n =>
      anisotropicTailRecursion D s z.1 j z.2) := by
  induction j with
  | zero => exact (anisotropicGridTerminalPotential_lipschitz D).continuous.comp continuous_snd
  | succ j ih =>
    simp_rw [anisotropicTailRecursion,anisotropicGaussianShift_eq_finiteStateStep]
    exact continuous_finiteStateGaussianStep_family (s.m (k+1-j))
      (fun z : Paper.Overlap×AnisotropicParameter n => anisotropicTailRecursion D s z.1 j)
      ((ih (by omega)).comp (continuous_fst.fst.prodMk continuous_snd))
      ‖anisotropicEnergyMap D‖₊
      (fun z => by
        rw [anisotropicTailRecursion_eq_clamped D s z.1 z.1.property (by omega)]
        exact anisotropicFinitePotential_lipschitz D _ _)
      (fun z : Paper.Overlap×AnisotropicParameter n =>
        Real.sqrt (max (z.1:ℝ) (s.q (k+2-j))-max (z.1:ℝ) (s.q (k+1-j))) • anisotropicUnitInput D)
      (by fun_prop) (fun z => z.2) continuous_snd

theorem continuous_anisotropicFiniteTailPotential_joint (D : AnisotropicSpinModel n)
    (s : RSBScheme k) :
    Continuous (fun z : Paper.Overlap×AnisotropicParameter n =>
      anisotropicFiniteTailPotential D s z.1 z.2) :=
  continuous_anisotropicTailRecursion_joint D s _ le_rfl

theorem continuous_anisotropicMeasureTailPotential_joint (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Continuous (fun z : Paper.Overlap×AnisotropicParameter n =>
      anisotropicMeasureTailPotential D μ z.1 z.2) := by
  apply (tendstoUniformly_anisotropicDyadicTailPotential D μ).continuous
  exact (Eventually.of_forall fun j => continuous_anisotropicTailRecursion_joint D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) _ le_rfl).frequently

theorem continuous_anisotropicFiniteTailDifferential_joint (D : AnisotropicSpinModel n)
    (s : RSBScheme k) :
    Continuous (fun z : Paper.Overlap×AnisotropicParameter n =>
      fderiv ℝ (anisotropicFiniteTailPotential D s z.1) z.2) := by
  apply continuous_fderiv_family_of_uniform_secondJet _
    (continuous_anisotropicFiniteTailPotential_joint D s)
    (contDiff_anisotropicFiniteTailPotential D s) (‖anisotropicEnergyMap D‖^2) (by positivity)
  intro q P
  change ‖iteratedFDeriv ℝ 2 (anisotropicFiniteTailPotential D s q) P‖ ≤ _
  unfold anisotropicFiniteTailPotential
  rw [anisotropicTailRecursion_eq_clamped D s q q.property le_rfl]
  exact norm_anisotropicFinitePotential_secondJet_le D _ _ P

theorem continuous_anisotropicFiniteTailSecondDifferential_joint (D : AnisotropicSpinModel n)
    (s : RSBScheme k) :
    Continuous (fun z : Paper.Overlap×AnisotropicParameter n =>
      fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s z.1)) z.2) := by
  apply continuous_fderiv_family_of_uniform_secondJet _
    (continuous_anisotropicFiniteTailDifferential_joint D s)
    (fun q => (contDiff_anisotropicFiniteTailPotential D s q).fderiv_right (m:=∞) (by simp))
    (8*‖anisotropicEnergyMap D‖^3) (by positivity)
  intro q P
  change ‖iteratedFDeriv ℝ 2 (fderiv ℝ (anisotropicFiniteTailPotential D s q)) P‖ ≤ _
  rw [norm_iteratedFDeriv_fderiv]
  unfold anisotropicFiniteTailPotential
  rw [anisotropicTailRecursion_eq_clamped D s q q.property le_rfl]
  exact norm_anisotropicFinitePotential_thirdJet_le D _ _ P

theorem continuous_anisotropicMeasureTailDifferential_joint (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Continuous (fun z : Paper.Overlap×AnisotropicParameter n =>
      fderiv ℝ (anisotropicMeasureTailPotential D μ z.1) z.2) := by
  apply (tendstoUniformly_anisotropicDyadicTailDifferential D μ).continuous
  exact (Eventually.of_forall fun j => continuous_anisotropicFiniteTailDifferential_joint D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))).frequently

theorem continuous_anisotropicMeasureTailSecondDifferential_joint (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Continuous (fun z : Paper.Overlap×AnisotropicParameter n =>
      fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ z.1)) z.2) := by
  apply (tendstoUniformly_anisotropicDyadicTailSecondDifferential D μ).continuous
  exact (Eventually.of_forall fun j => continuous_anisotropicFiniteTailSecondDifferential_joint D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))).frequently

theorem continuous_anisotropicMeasureTailMagnetization_joint (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Continuous (fun z : Paper.Overlap×AnisotropicParameter n =>
      anisotropicMeasureTailMagnetization D μ z.1 z.2) :=
  (anisotropicResponseMap n).continuous.comp (continuous_anisotropicMeasureTailDifferential_joint D μ)

end QuantitativeFollowup
