module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTerminalKernelSchemeAgreement
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPrefixTrimmedAgreement
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCrossMarkedLaw
public import QuantitativeFollowup.FollowupCavityOriginalVertexMarks
public import QuantitativeFollowup.FollowupCavityVertexMarks

@[expose] public section

/-! Whole-record finite/native vertex-mark agreement under the original
full initial disorder tilt. Each fresh spin uses the actual restarted
terminal kernel; all original fields and spins remain in the map. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingVertexState_energy {E S : Type} [Fintype S]
    (φ : E → FiniteStateField S) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) (H : E) (z : Records E S T) :
    φ (nativeStreamingVertexState v H z) =
      v.field (φ H) (observationTreeMap φ T z) := by
  induction v generalizing H with
  | root T => rfl
  | child v ih => exact ih z.1 z.2
  | left v ih => exact ih H z.1
  | right v ih => exact ih H z.2

theorem nativeStreamingMarkedLaw_map_base {A B S : Type}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace S]
    (P : Measure A) [IsProbabilityMeasure P]
    (κ : Kernel A S) [IsMarkovKernel κ] (η : Kernel B S) [IsMarkovKernel η]
    (φ : A → B) (hφ : Measurable φ) (hκ : κ = η.comap φ hφ) :
    (P ⊗ₘ κ).map (Prod.map φ id) = (P.map φ) ⊗ₘ η := by
  rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ (hφ.prodMap measurable_id),
    ←Kernel.map_prod_map _ _ hφ measurable_id, Kernel.map_id, hκ,
    Kernel.id_map hφ, ←Kernel.id_comap hφ, ←Kernel.comap_prod,
    ←Kernel.comp_deterministic_eq_comap, ←Measure.comp_assoc,
    Measure.deterministic_comp_eq_map hφ, ←Measure.compProd_eq_comp_prod]

theorem nativeStreamingSingleVertexKernel_scheme_energy
    (D : AnisotropicSpinModel n) (s : RSBScheme k) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (hj : j ≤ k+2) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingSingleVertexKernel D (Paper.parisiSchemeMeasure s)
      (anisotropicRecordedSchemeSchedule s) T v =
      (finiteCascadeSingleVertexKernel (fun _ : Configuration n => 0)
        (anisotropicSchemeMass s)
        (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) v).comap
          (Prod.map (anisotropicObservationEnergy D)
            (observationTreeMap (anisotropicObservationEnergy D) T))
          ((measurable_anisotropicObservationEnergy D).prodMap
            (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) T)) := by
  unfold nativeStreamingSingleVertexKernel finiteCascadeSingleVertexKernel
  rw [nativeStreamingObservationTerminalSpinKernel_scheme_energy D s v.depth
    (v.depth_le.trans hj)]
  ext z A hA
  simp only [Kernel.comap_apply, Function.uncurry, Prod.map_fst, Prod.map_snd]
  rw [nativeStreamingVertexState_energy (anisotropicObservationEnergy D) v z.1 z.2]

theorem nativeStreamingSingleVertexLaw_scheme_energy_prefix
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (hj : j ≤ k+2) (v : FiniteCascadeRecordVertex T) :
    (nativeStreamingSingleVertexLaw D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T v).map
      (Prod.map (Prod.map (anisotropicObservationEnergy D)
        (observationTreeMap (anisotropicObservationEnergy D) T)) id) =
      finiteCascadeSingleVertexMarkedLaw (fun _ : Configuration n => 0)
        (anisotropicSchemeMass s)
        (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) v
        (nativeStreamingFiniteRecordedPrefixLaw D s a T) := by
  haveI := finiteCascadeSingleVertexKernel_markov (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) v
  unfold nativeStreamingSingleVertexLaw
  rw [nativeStreamingMarkedLaw_map_base _ _ _ _
    ((measurable_anisotropicObservationEnergy D).prodMap
      (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) T))
    (nativeStreamingSingleVertexKernel_scheme_energy D s T hj v),
    nativeStreamingRecordedProfileLaw_scheme_energy_prefix D s a T hj]
  rfl

theorem nativeStreamingSingleVertexLaw_scheme_trimmed_energy
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1)) (v : FiniteCascadeRecordVertex T) :
    (nativeStreamingSingleVertexLaw D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T v).map
      (Prod.map (Prod.map (anisotropicObservationEnergy D)
        (observationTreeMap (anisotropicObservationEnergy D) T)) id) =
      anisotropicSingleVertexMarkedLaw D s a T.advance v := by
  rw [nativeStreamingSingleVertexLaw_scheme_energy_prefix D s a T (by omega) v]
  unfold anisotropicSingleVertexMarkedLaw
  rw [nativeStreamingFiniteRecordedPrefixLaw_trimmed D s a hq T]
  rfl

theorem nativeStreamingCrossVertexKernel_scheme_energy
    (D : AnisotropicSpinModel n) (s : RSBScheme k) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (hj : j ≤ k+2) (v w : FiniteCascadeRecordVertex T) :
    nativeStreamingCrossVertexKernel D (Paper.parisiSchemeMeasure s)
      (anisotropicRecordedSchemeSchedule s) T v w =
      (finiteCascadeCrossVertexPairKernel (fun _ : Configuration n => 0)
        (anisotropicSchemeMass s)
        (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) v w).comap
      (Prod.map (anisotropicObservationEnergy D)
        (observationTreeMap (anisotropicObservationEnergy D) T))
      ((measurable_anisotropicObservationEnergy D).prodMap
        (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) T)) := by
  haveI := finiteCascadeSingleVertexKernel_markov (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) v
  haveI := finiteCascadeSingleVertexKernel_markov (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) w
  unfold nativeStreamingCrossVertexKernel
  rw [nativeStreamingSingleVertexKernel_scheme_energy D s T hj v,
    nativeStreamingSingleVertexKernel_scheme_energy D s T hj w, ←Kernel.comap_prod]
  rfl

theorem nativeStreamingCrossVertexLaw_scheme_energy_prefix
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (hj : j ≤ k+2) (v w : FiniteCascadeRecordVertex T) :
    (nativeStreamingCrossVertexLaw D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T v w).map
      (Prod.map (Prod.map (anisotropicObservationEnergy D)
        (observationTreeMap (anisotropicObservationEnergy D) T)) id) =
      finiteCascadeCrossVertexMarkedLaw (fun _ : Configuration n => 0)
        (anisotropicSchemeMass s)
        (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) v w
        (nativeStreamingFiniteRecordedPrefixLaw D s a T) := by
  haveI := finiteCascadeCrossVertexPairKernel_markov (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) v w
  unfold nativeStreamingCrossVertexLaw
  rw [nativeStreamingMarkedLaw_map_base _ _ _ _
    ((measurable_anisotropicObservationEnergy D).prodMap
      (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) T))
    (nativeStreamingCrossVertexKernel_scheme_energy D s T hj v w),
    nativeStreamingRecordedProfileLaw_scheme_energy_prefix D s a T hj]
  rfl

theorem nativeStreamingCrossVertexLaw_scheme_trimmed_energy
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1)) (v w : FiniteCascadeRecordVertex T) :
    (nativeStreamingCrossVertexLaw D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T v w).map
      (Prod.map (Prod.map (anisotropicObservationEnergy D)
        (observationTreeMap (anisotropicObservationEnergy D) T)) id) =
      anisotropicCrossVertexMarkedLaw D s a T.advance v w := by
  rw [nativeStreamingCrossVertexLaw_scheme_energy_prefix D s a T (by omega) v w]
  unfold anisotropicCrossVertexMarkedLaw
  rw [nativeStreamingFiniteRecordedPrefixLaw_trimmed D s a hq T]

end QuantitativeFollowup
