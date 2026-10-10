module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingVertexSchemeAgreement
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCurrentPairLaw

@[expose] public section

/-! The current pair consists of two genuine independent continuations
at one retained vertex. Its complete finite/native record law therefore
agrees with the diagonal instance of the actual cross-vertex law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingCurrentPairKernel_eq_cross
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (v : FiniteCascadeRecordVertex T) :
    nativeStreamingCurrentPairKernel D μ q T v =
      nativeStreamingCrossVertexKernel D μ q T v v := by
  unfold nativeStreamingCurrentPairKernel nativeStreamingCrossVertexKernel
    nativeStreamingSingleVertexKernel
  rw [←Kernel.comap_prod]

theorem nativeStreamingCurrentPairLaw_eq_cross
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (v : FiniteCascadeRecordVertex T) :
    nativeStreamingCurrentPairLaw D μ a q T v =
      nativeStreamingCrossVertexLaw D μ a q T v v := by
  unfold nativeStreamingCurrentPairLaw nativeStreamingCrossVertexLaw
  rw [nativeStreamingCurrentPairKernel_eq_cross]

theorem nativeStreamingCurrentPairLaw_scheme_energy_prefix
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (hj : j ≤ k+2) (v : FiniteCascadeRecordVertex T) :
    (nativeStreamingCurrentPairLaw D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T v).map
      (Prod.map (Prod.map (anisotropicObservationEnergy D)
        (observationTreeMap (anisotropicObservationEnergy D) T)) id) =
      finiteCascadeCrossVertexMarkedLaw (fun _ : Configuration n => 0)
        (anisotropicSchemeMass s)
        (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) v v
        (nativeStreamingFiniteRecordedPrefixLaw D s a T) := by
  rw [nativeStreamingCurrentPairLaw_eq_cross]
  exact nativeStreamingCrossVertexLaw_scheme_energy_prefix D s a T hj v v

theorem nativeStreamingCurrentPairLaw_scheme_trimmed_energy
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1)) (v : FiniteCascadeRecordVertex T) :
    (nativeStreamingCurrentPairLaw D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T v).map
      (Prod.map (Prod.map (anisotropicObservationEnergy D)
        (observationTreeMap (anisotropicObservationEnergy D) T)) id) =
      anisotropicCrossVertexMarkedLaw D s a T.advance v v := by
  rw [nativeStreamingCurrentPairLaw_eq_cross]
  exact nativeStreamingCrossVertexLaw_scheme_trimmed_energy D s a hq T v v

end QuantitativeFollowup
