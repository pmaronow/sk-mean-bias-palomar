module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFiniteTreeAgreement
public import QuantitativeFollowup.FollowupCavityRootCharges

@[expose] public section

/-! The physical zero-width initial edge identifies the retained-prefix
law with the legacy finite trimmed law. The full original initial tilt
is reduced only by the proved zero-noise potential identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingFiniteRecordedPrefixLaw_trimmed
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1)) :
    nativeStreamingFiniteRecordedPrefixLaw D s a T =
      anisotropicTrimmedRecordedTreeLaw D s a T.advance := by
  have hz : (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s (k+1))=0 := by
    rw [anisotropicSchemeInput_root_zero D s hq]
    ext x σ
    simp
  unfold nativeStreamingFiniteRecordedPrefixLaw
  rw [anisotropicFiniteInitialLaw_energy]
  unfold anisotropicTrimmedRecordedTreeLaw finiteCascadeTreeGaussianJointLaw
  change ((finiteStateGaussianRawKernel (anisotropicRootEnergyMap D) 0).tilted
    (fun H => a*finiteStateGaussianTerminalCascade (fun _ : Configuration n => 0)
      (anisotropicSchemeMass s)
      (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) (k+2) H)) ⊗ₘ _ =
    ((finiteStateGaussianRawKernel (anisotropicRootEnergyMap D) 0).tilted
    (fun H => a*finiteStateGaussianTerminalCascade (fun _ : Configuration n => 0)
      (anisotropicSchemeMass s)
      (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) (k+1) H)) ⊗ₘ _
  have hp : (fun H => a*finiteStateGaussianTerminalCascade (fun _ : Configuration n => 0)
      (anisotropicSchemeMass s)
      (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) (k+2) H) =
      (fun H => a*finiteStateGaussianTerminalCascade (fun _ : Configuration n => 0)
      (anisotropicSchemeMass s)
      (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) (k+1) H) := by
    funext H
    rw [show k+2=(k+1)+1 by omega,
      finiteStateGaussianTerminalCascade_zero_root_step _ _ _ (k+1) hz]
  rw [hp]

theorem nativeStreamingRecordedProfileLaw_scheme_prefix_trimmed_energy
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1)) :
    (anisotropicRecordedProfileTreeLaw D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T).map
        (Prod.map (anisotropicObservationEnergy D)
          (observationTreeMap (anisotropicObservationEnergy D) T)) =
      anisotropicTrimmedRecordedTreeLaw D s a T.advance :=
  (nativeStreamingRecordedProfileLaw_scheme_energy_prefix D s a T (by omega)).trans
    (nativeStreamingFiniteRecordedPrefixLaw_trimmed D s a hq T)

end QuantitativeFollowup
