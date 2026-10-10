module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexPatternsMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternVertexCoherenceCross

@[expose] public section

/-! Fixed original/fresh, current, and vertex/vertex cross patterns are
literal terminal tests on genuine enlarged genealogies.  The terminal
projections preserve every original spin, and their record identities
retain the complete old record before integration.  No restrictions on
distinct clocks or vertices are needed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def nativeStreamingPatternCrossTerminalProjection {S : Type}
    {T : FiniteTerminalGenealogy J} (v w : FiniteCascadeRecordVertex T)
    (σ : TerminalSpins S (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    TerminalSpins S T × (S × S) :=
  let z := nativeStreamingGeneratedVertexTerminalProjection .single
    (finiteCascadeContinuationVertexEmbed observationLinearTree v w) σ
  let z' := nativeStreamingGeneratedVertexTerminalProjection .single v z.1
  (z'.1,(z'.2,z.2))

theorem nativeStreamingPatternCrossTerminalProjection_record {E S : Type}
    {T : FiniteTerminalGenealogy J} (v w : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    nativeStreamingPatternCrossTerminalProjection v w (finiteCascadeRecordTerminalSpins _ z) =
      (finiteCascadeRecordTerminalSpins T
        (finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z).1,
        (finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z).2) := by
  have hfirst := nativeStreamingGeneratedVertexTerminalProjection_record
    (E:=E) (S:=S) .single (finiteCascadeContinuationVertexEmbed observationLinearTree v w) z
  dsimp only [NativeStreamingGeneratedVertexKind.continuation,
    NativeStreamingGeneratedVertexKind.recordMark] at hfirst
  dsimp only [nativeStreamingPatternCrossTerminalProjection]
  rw [hfirst]
  dsimp only
  have hsecond := nativeStreamingGeneratedVertexTerminalProjection_record (E:=E) (S:=S)
    .single v
    (finiteCascadeContinuationExtract observationLinearTree observationLinearSpin
      (finiteCascadeContinuationVertexEmbed observationLinearTree v w) z).1
  dsimp only [NativeStreamingGeneratedVertexKind.continuation,
    NativeStreamingGeneratedVertexKind.recordMark] at hsecond
  rw [hsecond]

def nativeStreamingPatternVertexTerminalTest
    (k : NativeStreamingGeneratedVertexKind) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × k.Mark (Configuration n) → ℝ) :
    TerminalSpins (Configuration n) (finiteCascadeContinuationGraft k.continuation v) → ℝ :=
  G ∘ nativeStreamingGeneratedVertexTerminalProjection k v

def nativeStreamingPatternCrossTerminalTest (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    TerminalSpins (Configuration n)
      (finiteCascadeCrossContinuationGraft observationLinearTree v w) → ℝ :=
  G ∘ nativeStreamingPatternCrossTerminalProjection v w

theorem nativeStreamingActualContinuationTerminalMoment_eq_oldTerminalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (k : NativeStreamingGeneratedVertexKind)
    (G : TerminalSpins (Configuration (n+1)) T × k.Mark (Configuration (n+1)) → ℝ) :
    nativeStreamingTerminalMarkMoment
      (nativeStreamingActualContinuationProbability D μ a q k.continuation k.recordMark T v) G =
      nativeStreamingOldTerminalExpectation D μ a q (finiteCascadeContinuationGraft k.continuation v)
        (nativeStreamingPatternVertexTerminalTest k T v G) := by
  exact (nativeStreamingGeneratedVertexMoment_eq_terminalMarkMoment D μ a q T v k G).symm

theorem nativeStreamingCrossVertexTerminalMoment_eq_oldTerminalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration (n+1)) T × (Configuration (n+1) × Configuration (n+1)) → ℝ) :
    nativeStreamingTerminalMarkMoment (nativeStreamingCrossVertexProbability D μ a q T v w) G =
      nativeStreamingOldTerminalExpectation D μ a q
        (finiteCascadeCrossContinuationGraft observationLinearTree v w)
        (nativeStreamingPatternCrossTerminalTest T v w G) := by
  let ψ := fun z : AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1))
        (finiteCascadeCrossContinuationGraft observationLinearTree v w) =>
    ((z.1,(finiteCascadeCrossContinuationExtract observationLinearTree
      observationLinearSpin v w z.2).1),
      (finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z.2).2)
  have he := measurable_finiteCascadeCrossContinuationExtract (E:=AnisotropicObservationState (n+1))
    (S:=Configuration (n+1)) observationLinearTree observationLinearSpin
    (fun j => measurable_observationLinearSpin j) v w
  have hm : Measurable ψ :=
    (measurable_fst.prodMk (he.fst.comp measurable_snd)).prodMk (he.snd.comp measurable_snd)
  have hc : Continuous (fun z : ((AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T) ×
        (Configuration (n+1) × Configuration (n+1))) =>
      G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (continuous_of_discreteTopology (f:=G)).comp
      (((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_fst.snd).prodMk continuous_snd)
  unfold nativeStreamingTerminalMarkMoment nativeStreamingCrossVertexProbability
  rw [ProbabilityMeasure.toMeasure_map,integral_map hm.aemeasurable hc.aestronglyMeasurable]
  unfold nativeStreamingOldTerminalExpectation nativeStreamingPatternCrossTerminalTest
  apply integral_congr_ae
  exact .of_forall fun z => congrArg G
    (nativeStreamingPatternCrossTerminalProjection_record v w z.2).symm

theorem nativeStreamingPatternMoment_originalFresh_terminalRepresentation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D μ a q T F (.originalFresh i (.vertex v)) =
      nativeStreamingOldTerminalExpectation D μ a q
        (finiteCascadeContinuationGraft observationLinearTree v)
        (nativeStreamingPatternVertexTerminalTest .single T v
          (nativeStreamingOriginalFreshSpinTest T F i
            (q (finiteCascadeCommonPathDepth T (observationLeafVertex T i) v)))) := by
  exact (nativeStreamingGeneratedVertexMoment_originalFresh D μ a q T v F i).symm

theorem nativeStreamingPatternMoment_current_terminalRepresentation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D μ a q T F (.current (.vertex v)) =
      nativeStreamingOldTerminalExpectation D μ a q
        (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree v)
        (nativeStreamingPatternVertexTerminalTest .current T v
          (nativeStreamingDefectSpinTest T F (q v.depth))) := by
  exact (nativeStreamingGeneratedVertexMoment_current D μ a q T v F).symm

theorem nativeStreamingPatternMoment_cross_vertices_terminalRepresentation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v w : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) (.vertex w)) =
      nativeStreamingOldTerminalExpectation D μ a q
        (finiteCascadeCrossContinuationGraft observationLinearTree v w)
        (nativeStreamingPatternCrossTerminalTest T v w
          (nativeStreamingDefectSpinTest T F (q (finiteCascadeCommonPathDepth T v w)))) := by
  exact nativeStreamingCrossVertexTerminalMoment_eq_oldTerminalExpectation D μ a q T v w _

end QuantitativeFollowup
