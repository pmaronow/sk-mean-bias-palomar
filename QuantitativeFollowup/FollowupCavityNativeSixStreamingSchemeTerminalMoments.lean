module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCurrentSchemeAgreement
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCurrentPairContinuity
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTerminalMarkMoments
public import QuantitativeFollowup.AnisotropicObservationSchemeEmbedding

@[expose] public section

/-! Actual bounded terminal-spin moments transport with the full old
record under finite/native scheme agreement. Fresh marks remain unchanged
by the energy map. No equality of moments is supplied as a premise to the
three actual scheme consumers. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem energy_map_terminal_integral
    {A : Type} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (D : AnisotropicSpinModel n) (T : FiniteTerminalGenealogy J)
    (P : Measure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) × A))
    (Q : Measure ((FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) T) × A))
    (hmap : P.map
      (Prod.map (Prod.map (anisotropicObservationEnergy D)
        (observationTreeMap (anisotropicObservationEnergy D) T)) id) = Q)
    (G : TerminalSpins (Configuration n) T × A → ℝ) :
    (∫z, G (finiteCascadeRecordTerminalSpins T z.1.2,z.2) ∂P) =
      ∫z, G (finiteCascadeRecordTerminalSpins T z.1.2,z.2) ∂Q := by
  have hφ : Measurable (Prod.map (Prod.map (anisotropicObservationEnergy D)
      (observationTreeMap (S := Configuration n) (anisotropicObservationEnergy D) T))
      (id : A → A)) :=
    ((measurable_anisotropicObservationEnergy D).prodMap
      (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) T)).prodMap
        measurable_id
  have hG : Measurable (fun z : ((FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) T) × A) =>
      G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (measurable_of_finite G).comp
      (((measurable_finiteCascadeRecordTerminalSpins T).comp
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have H := integral_map (μ := P) hφ.aemeasurable hG.aestronglyMeasurable
  rw [hmap] at H
  simpa only [Prod.map_apply', Prod.map_fst, Prod.map_snd,
    finiteCascadeRecordTerminalSpins_treeMap, id_eq] using H.symm

theorem nativeStreamingSchemeSchedule_zero (s : RSBScheme k) :
    anisotropicRecordedSchemeSchedule s 0 = 1 := by
  apply Subtype.ext
  rw [anisotropicRecordedSchemeSchedule,Nat.sub_zero,
    anisotropicFiniteMeshNode_coe s _ le_rfl,s.q_top]
  rfl

theorem nativeStreamingSingleTerminalMoment_scheme_trimmed
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1)) (v : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × Configuration n → ℝ) :
    nativeStreamingTerminalMarkMoment
      (nativeStreamingSingleVertexProbability D (Paper.parisiSchemeMeasure s) a
        (anisotropicRecordedSchemeSchedule s) T v) G =
      ∫z, G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂anisotropicSingleVertexMarkedLaw D s a T.advance v := by
  unfold nativeStreamingTerminalMarkMoment
  rw [nativeStreamingSingleVertexProbability_eq_law D _ a _
    (anisotropicRecordedSchemeSchedule_antitone s) (nativeStreamingSchemeSchedule_zero s) T v]
  exact energy_map_terminal_integral D T _ _
    (nativeStreamingSingleVertexLaw_scheme_trimmed_energy D s a hq T v) G

theorem nativeStreamingCrossTerminalMoment_scheme_trimmed
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1)) (v w : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    nativeStreamingTerminalMarkMoment
      (nativeStreamingCrossVertexProbability D (Paper.parisiSchemeMeasure s) a
        (anisotropicRecordedSchemeSchedule s) T v w) G =
      ∫z, G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂anisotropicCrossVertexMarkedLaw D s a T.advance v w := by
  unfold nativeStreamingTerminalMarkMoment
  rw [nativeStreamingCrossVertexProbability_eq_law D _ a _
    (anisotropicRecordedSchemeSchedule_antitone s) (nativeStreamingSchemeSchedule_zero s) T v w]
  exact energy_map_terminal_integral D T _ _
    (nativeStreamingCrossVertexLaw_scheme_trimmed_energy D s a hq T v w) G

theorem nativeStreamingCurrentTerminalMoment_scheme_trimmed
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1)) (v : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    nativeStreamingTerminalMarkMoment
      (nativeStreamingCurrentPairProbability D (Paper.parisiSchemeMeasure s) a
        (anisotropicRecordedSchemeSchedule s) T v) G =
      ∫z, G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂anisotropicCrossVertexMarkedLaw D s a T.advance v v := by
  unfold nativeStreamingTerminalMarkMoment
  rw [nativeStreamingCurrentPairProbability_eq_law D _ a _
    (anisotropicRecordedSchemeSchedule_antitone s) (nativeStreamingSchemeSchedule_zero s) T v]
  exact energy_map_terminal_integral D T _ _
    (nativeStreamingCurrentPairLaw_scheme_trimmed_energy D s a hq T v) G

end QuantitativeFollowup
