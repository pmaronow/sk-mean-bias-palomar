module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeVertexEndpoint
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeEndpointCoherenceLaws
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFuturePairContinuity
public import FourPapersCommon.FiniteObservationRefinementTerminalLeaves

@[expose] public section

/-! Exact observation refinement preserves arbitrary finite terminal tests
of the original record together with genuine ancestral fresh marks. These
are actual law identities before any attachment charges are regrouped. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def nativeStreamingRefinedTerminalTest {S : Type} (d : ℕ → ℕ)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins S T → ℝ) :
    TerminalSpins S (observationRefineTree d T) → ℝ :=
  F ∘ observationRefinementTerminalProject d T rfl

theorem nativeStreamingRefinementTerminalProject_record {E S : Type}
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (z : Records E S (observationRefineTree d T)) :
    observationRefinementTerminalProject d T rfl
        (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z) =
      finiteCascadeRecordTerminalSpins T (observationRefinementProject d T z) := by
  simpa only [observationTreeDepthCast,observationRefinementDepthProject,
    observationRecordDepthCast,Function.comp_apply,id_eq] using
    observationRefinementTerminalProject_record d T rfl z

private theorem terminal_refinement_marked_integral {A : Type}
    [MeasurableSpace A] [MeasurableSingletonClass A] [Finite A]
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (P : Measure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n)
        (observationRefineTree d T)) × A))
    (G : TerminalSpins (Configuration n) T × A → ℝ) :
    (∫z,G (observationRefinementTerminalProject d T rfl
        (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2),z.2) ∂P) =
      ∫z,G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂P.map (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2)) := by
  have hm : Measurable (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n)
        (observationRefineTree d T)) × A) =>
      ((z.1.1,observationRefinementProject d T z.1.2),z.2)) :=
    (measurable_fst.fst.prodMk
      ((measurable_observationRefinementProject d T).comp measurable_fst.snd)).prodMk measurable_snd
  have hG : Measurable (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) × A) =>
      G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (measurable_of_finite G).comp
      (((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_fst.snd).prodMk measurable_snd)
  have he := integral_map (μ:=P) hm.aemeasurable hG.aestronglyMeasurable
  simpa only [Function.comp_def,nativeStreamingRefinementTerminalProject_record] using he.symm

theorem nativeStreamingOldTerminalIntegral_refinement
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration n) T → ℝ) :
    (∫z,nativeStreamingRefinedTerminalTest d T F
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.2)
      ∂anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T)) =
      ∫z,F (finiteCascadeRecordTerminalSpins T z.2)
        ∂anisotropicRecordedProfileTreeLaw D μ a q T := by
  have hm : Measurable (Prod.map (id : AnisotropicObservationState n → AnisotropicObservationState n)
      (observationRefinementProject (E:=AnisotropicObservationState n) (S:=Configuration n) d T)) :=
    measurable_id.prodMap (measurable_observationRefinementProject d T)
  have hF : Measurable (fun z : AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T =>
      F (finiteCascadeRecordTerminalSpins T z.2)) :=
    (measurable_of_finite F).comp ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd)
  have he := integral_map (μ:=anisotropicRecordedProfileTreeLaw D μ a Q
      (observationRefineTree d T)) hm.aemeasurable hF.aestronglyMeasurable
  rw [anisotropicRecordedProfileTreeLaw_refinement D μ a q Q d hQ hlevels T] at he
  simpa only [nativeStreamingRefinedTerminalTest,Function.comp_def,Prod.map_snd,
    nativeStreamingRefinementTerminalProject_record] using he.symm

theorem nativeStreamingSingleVertexTerminalIntegral_refinement
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × Configuration n → ℝ) :
    (∫z,G (observationRefinementTerminalProject d T rfl
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2),z.2)
      ∂nativeStreamingSingleVertexLaw D μ a Q (observationRefineTree d T)
        (nativeStreamingRefinementVertexEmbed d T v)) =
      ∫z,G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂nativeStreamingSingleVertexLaw D μ a q T v := by
  rw [terminal_refinement_marked_integral d T,
    nativeStreamingSingleVertexLaw_refinement D μ a q Q d hQ hlevels T v]

theorem nativeStreamingCrossVertexTerminalIntegral_refinement
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (v w : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    (∫z,G (observationRefinementTerminalProject d T rfl
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2),z.2)
      ∂nativeStreamingCrossVertexLaw D μ a Q (observationRefineTree d T)
        (nativeStreamingRefinementVertexEmbed d T v) (nativeStreamingRefinementVertexEmbed d T w)) =
      ∫z,G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂nativeStreamingCrossVertexLaw D μ a q T v w := by
  rw [terminal_refinement_marked_integral d T,
    nativeStreamingCrossVertexLaw_refinement D μ a q Q d hQ hlevels T v w]

theorem nativeStreamingCurrentVertexTerminalIntegral_refinement
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    (∫z,G (observationRefinementTerminalProject d T rfl
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2),z.2)
      ∂nativeStreamingCurrentPairLaw D μ a Q (observationRefineTree d T)
        (nativeStreamingRefinementVertexEmbed d T v)) =
      ∫z,G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂nativeStreamingCurrentPairLaw D μ a q T v := by
  rw [terminal_refinement_marked_integral d T,
    nativeStreamingCurrentPairLaw_refinement D μ a q Q d hQ hlevels T v]

theorem nativeStreamingFutureVertexTerminalIntegral_refinement
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) (r : Paper.Overlap)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    (∫z,G (observationRefinementTerminalProject d T rfl
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2),z.2)
      ∂nativeStreamingFuturePairLaw D μ a Q (observationRefineTree d T)
        (nativeStreamingRefinementVertexEmbed d T v) r) =
      ∫z,G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂nativeStreamingFuturePairLaw D μ a q T v r := by
  rw [terminal_refinement_marked_integral d T,
    nativeStreamingFuturePairLaw_refinement D μ a q Q d hQ hlevels T v r]

end QuantitativeFollowup
