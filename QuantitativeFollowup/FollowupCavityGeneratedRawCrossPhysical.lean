module
public import QuantitativeFollowup.FollowupCavityGeneratedRawCrossObservation
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSelectedCrossPatternMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossVertexPatternsTerminal

@[expose] public section

/-! The raw double continuation keeps the complete original record, its
terminal test, and both new terminal spins. Its pair clock is the genuine
common clock of the two original selected locations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {J n : ℕ}

def cavityGeneratedRawCrossTree (T : FiniteTerminalGenealogy J)
    (s t : CavityGeneratedRawCrossSite T) (k : NativeStreamingGeneratedCrossEdgeChart) :=
  finiteCascadeCrossContinuationGraft observationLinearTree
    (cavityGeneratedRawCrossObservationFirst T s t k)
    (cavityGeneratedRawCrossObservationSecond T s t k)

def cavityGeneratedRawCrossRecordProjection {E S : Type}
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (z : E × Records E S (cavityGeneratedRawCrossTree T s t k)) :
    (E × Records E S T) × (S×S) :=
  let e := finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin
    (cavityGeneratedRawCrossObservationFirst T s t k)
    (cavityGeneratedRawCrossObservationSecond T s t k) z.2
  ((z.1,observationRefinementProject (cavityGeneratedRawCrossSubdivision T s t) T e.1),e.2)

theorem measurable_cavityGeneratedRawCrossRecordProjection {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S]
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    Measurable (cavityGeneratedRawCrossRecordProjection (E:=E) (S:=S) T s t k) := by
  have he : Measurable (fun z : E × Records E S (cavityGeneratedRawCrossTree T s t k)=>
      finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin
        (cavityGeneratedRawCrossObservationFirst T s t k)
        (cavityGeneratedRawCrossObservationSecond T s t k) z.2) :=
    (measurable_finiteCascadeCrossContinuationExtract (E:=E) (S:=S)
      observationLinearTree observationLinearSpin (fun j=>measurable_observationLinearSpin j)
      (cavityGeneratedRawCrossObservationFirst T s t k)
      (cavityGeneratedRawCrossObservationSecond T s t k)).comp measurable_snd
  exact (measurable_fst.prodMk ((measurable_observationRefinementProject
    (cavityGeneratedRawCrossSubdivision T s t) T).comp he.fst)).prodMk he.snd

def cavityGeneratedRawCrossTerminalProjection {S : Type}
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (σ : TerminalSpins S (cavityGeneratedRawCrossTree T s t k)) :
    TerminalSpins S T × (S×S) :=
  let e := nativeStreamingGeneratedCrossVertexTerminalProjection
    (cavityGeneratedRawCrossObservationFirst T s t k)
    (cavityGeneratedRawCrossObservationSecond T s t k) σ
  (observationRefinementTerminalProject (cavityGeneratedRawCrossSubdivision T s t) T rfl e.1,e.2)

theorem cavityGeneratedRawCrossTerminalProjection_record {E S : Type}
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (z : E × Records E S (cavityGeneratedRawCrossTree T s t k)) :
    cavityGeneratedRawCrossTerminalProjection T s t k
      (finiteCascadeRecordTerminalSpins (cavityGeneratedRawCrossTree T s t k) z.2)=
      (finiteCascadeRecordTerminalSpins T (cavityGeneratedRawCrossRecordProjection T s t k z).1.2,
        (cavityGeneratedRawCrossRecordProjection T s t k z).2) := by
  have H := nativeStreamingGeneratedCrossVertexTerminalProjection_record
    (cavityGeneratedRawCrossObservationFirst T s t k)
    (cavityGeneratedRawCrossObservationSecond T s t k) z.2
  have H' := congrArg (fun e : TerminalSpins S (cavityGeneratedRawCrossObservationTree T s t) × (S×S)=>
    (observationRefinementTerminalProject (cavityGeneratedRawCrossSubdivision T s t) T rfl e.1,e.2)) H
  simpa only [cavityGeneratedRawCrossTerminalProjection,cavityGeneratedRawCrossRecordProjection,
    cavityGeneratedRawCrossObservationTree,cavityGeneratedRawCrossTree,
    nativeStreamingRefinementTerminalProject_record] using H'

theorem cavityGeneratedRawCross_full_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart) (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (hzero : q 0=1) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell q T s r)
    (hl : cavityGeneratedRawCrossCell q T t l)
    (hk : cavityGeneratedRawCrossChartHolds T s t k r l) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (cavityGeneratedRawCrossObservationClock T s t q r l)
      (cavityGeneratedRawCrossTree T s t k)).map
        (cavityGeneratedRawCrossRecordProjection T s t k)=
      (nativeStreamingOriginCrossProbability D μ a q T
        (cavityGeneratedRawCrossOrigin T s r) (cavityGeneratedRawCrossOrigin T t l) : Measure _) := by
  let Q := cavityGeneratedRawCrossObservationClock T s t q r l
  let R := cavityGeneratedRawCrossObservationTree T s t
  let v := cavityGeneratedRawCrossObservationFirst T s t k
  let w := cavityGeneratedRawCrossObservationSecond T s t k
  let A : AnisotropicObservationState n × Records (AnisotropicObservationState n)
      (Configuration n) (cavityGeneratedRawCrossTree T s t k) →
      (AnisotropicObservationState n × Records (AnisotropicObservationState n)
        (Configuration n) R) × (Configuration n×Configuration n) :=
    fun z=>((z.1,(finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z.2).1),
      (finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z.2).2)
  let B : (AnisotropicObservationState n × Records (AnisotropicObservationState n)
      (Configuration n) R) × (Configuration n×Configuration n) →
      (AnisotropicObservationState n × Records (AnisotropicObservationState n)
        (Configuration n) T) × (Configuration n×Configuration n) :=
    fun z=>((z.1.1,observationRefinementProject (cavityGeneratedRawCrossSubdivision T s t) T z.1.2),z.2)
  have he := measurable_finiteCascadeCrossContinuationExtract (E:=AnisotropicObservationState n)
    (S:=Configuration n) observationLinearTree observationLinearSpin
      (fun j=>measurable_observationLinearSpin j) v w
  have hA : Measurable A := (measurable_fst.prodMk (he.fst.comp measurable_snd)).prodMk
    (he.snd.comp measurable_snd)
  have hB : Measurable B := (measurable_fst.fst.prodMk
    ((measurable_observationRefinementProject (cavityGeneratedRawCrossSubdivision T s t) T).comp
      measurable_fst.snd)).prodMk measurable_snd
  have hQ : Antitone Q := cavityGeneratedRawCrossObservation_antitone T s t q hq r l hr hl
  have hQ0 : Q 0=1 := by
    have H := cavityGeneratedRawCrossObservation_refinement T s t q r l 0
    exact H.trans hzero
  change (anisotropicRecordedProfileTreeLaw D μ a Q _).map (B ∘ A)=_
  have hg : (anisotropicRecordedProfileTreeLaw D μ a Q (cavityGeneratedRawCrossTree T s t k)).map A=
      nativeStreamingCrossVertexLaw D μ a Q R v w :=
    nativeStreamingCrossVertexLaw_eq_graft D μ a Q hQ hQ0 R v w
  rw [←Measure.map_map hB hA,hg]
  exact cavityGeneratedRawCrossObservation_full_record_law D μ a T s t k q hq hzero r l hr hl hk

theorem cavityGeneratedRawCross_terminal_receiver
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart) (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (hzero : q 0=1) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell q T s r)
    (hl : cavityGeneratedRawCrossCell q T t l)
    (hk : cavityGeneratedRawCrossChartHolds T s t k r l)
    (G : TerminalSpins (Configuration n) T × (Configuration n×Configuration n) → ℝ) :
    (∫z,G (cavityGeneratedRawCrossTerminalProjection T s t k
      (finiteCascadeRecordTerminalSpins (cavityGeneratedRawCrossTree T s t k) z.2))
      ∂anisotropicRecordedProfileTreeLaw D μ a
        (cavityGeneratedRawCrossObservationClock T s t q r l) (cavityGeneratedRawCrossTree T s t k))=
      nativeStreamingTerminalMarkMoment
        (nativeStreamingOriginCrossProbability D μ a q T
          (cavityGeneratedRawCrossOrigin T s r) (cavityGeneratedRawCrossOrigin T t l)) G := by
  let P := anisotropicRecordedProfileTreeLaw D μ a
    (cavityGeneratedRawCrossObservationClock T s t q r l) (cavityGeneratedRawCrossTree T s t k)
  let f : (AnisotropicObservationState n × Records (AnisotropicObservationState n)
      (Configuration n) T) × (Configuration n×Configuration n) → ℝ :=
    fun z=>G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
  have hf : Measurable f := (measurable_of_finite G).comp
    (((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_fst.snd).prodMk measurable_snd)
  have H := integral_map (μ:=P) (measurable_cavityGeneratedRawCrossRecordProjection T s t k).aemeasurable
    hf.aestronglyMeasurable
  have hp := cavityGeneratedRawCross_full_record_law D μ a T s t k q hq hzero r l hr hl hk
  rw [hp] at H
  refine Eq.trans ?_ H.symm
  apply integral_congr_ae
  exact .of_forall fun z=>congrArg G (cavityGeneratedRawCrossTerminalProjection_record T s t k z)

theorem cavityGeneratedRawCrossObservation_common_clock
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart) (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell q T s r)
    (hl : cavityGeneratedRawCrossCell q T t l)
    (hk : cavityGeneratedRawCrossChartHolds T s t k r l) :
    cavityGeneratedRawCrossObservationClock T s t q r l
      (finiteCascadeCommonPathDepth (cavityGeneratedRawCrossObservationTree T s t)
        (cavityGeneratedRawCrossObservationFirst T s t k)
        (cavityGeneratedRawCrossObservationSecond T s t k))=
      nativeStreamingOriginCommonClock q T
        (cavityGeneratedRawCrossOrigin T s r) (cavityGeneratedRawCrossOrigin T t l) := by
  have hQ := cavityGeneratedRawCrossObservation_antitone T s t q hq r l hr hl
  have hlevels := cavityGeneratedRawCrossObservation_refinement T s t q r l
  rcases s with v | e <;> rcases t with w | f
  · change q (finiteCascadeCommonPathDepth (observationRefineTree (fun _=>0) T)
      (nativeStreamingRefinementVertexEmbed (fun _=>0) T v)
      (nativeStreamingRefinementVertexEmbed (fun _=>0) T w))=q (finiteCascadeCommonPathDepth T v w)
    rw [nativeStreamingRefinementVertexEmbed_commonPathDepth]
    exact hlevels _
  · have hp : 0<nativeStreamingEdgeSubdivision f.depth f.depth := by simp [nativeStreamingEdgeSubdivision]
    have hm : nativeStreamingEdgeSchedule q f.depth l
        (observationRefinementDepth (nativeStreamingEdgeSubdivision f.depth) f.depth+0+1)=l := by
      simp [nativeStreamingEdgeSubdivision_depth,nativeStreamingEdgeSchedule]
    have H := nativeStreamingEdgeOldVertex_commonPathClock_eq_mark (nativeStreamingEdgeSubdivision f.depth) q
      (nativeStreamingEdgeSchedule q f.depth l) T (fun i _=>hlevels i) v f 0 hp l hm
    simpa only [nativeStreamingOriginCommonClock,cavityGeneratedRawCrossOrigin,
      cavityGeneratedRawCrossObservationClock,cavityGeneratedRawCrossObservationTree,
      cavityGeneratedRawCrossSubdivision,cavityGeneratedRawCrossObservationFirst,
      cavityGeneratedRawCrossObservationSecond] using H
  · have hp : 0<nativeStreamingEdgeSubdivision e.depth e.depth := by simp [nativeStreamingEdgeSubdivision]
    change nativeStreamingEdgeSchedule q e.depth r
      (finiteCascadeCommonPathDepth (observationRefineTree (nativeStreamingEdgeSubdivision e.depth) T)
        (nativeStreamingEdgeSelectedVertex (nativeStreamingEdgeSubdivision e.depth) e 0)
        (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T w))=_
    rw [nativeStreamingSelectedGeometry_commonPathDepth_symm]
    have hm : nativeStreamingEdgeSchedule q e.depth r
        (observationRefinementDepth (nativeStreamingEdgeSubdivision e.depth) e.depth+0+1)=r := by
      simp [nativeStreamingEdgeSubdivision_depth,nativeStreamingEdgeSchedule]
    have H := nativeStreamingEdgeOldVertex_commonPathClock_eq_mark (nativeStreamingEdgeSubdivision e.depth) q
      (nativeStreamingEdgeSchedule q e.depth r) T (fun i _=>hlevels i) w e 0 hp r hm
    simpa only [nativeStreamingOriginCommonClock,cavityGeneratedRawCrossOrigin] using H
  · have hp : k.firstSlot<nativeStreamingPairObservationSubdivision e.depth := k.firstSlot_lt
    have hj : k.secondSlot<nativeStreamingPairObservationSubdivision f.depth := k.secondSlot_lt
    have H := nativeStreamingEdgeSelectedVertex_commonPathClock nativeStreamingPairObservationSubdivision q
      (nativeStreamingPairObservationSchedule q e.depth f.depth r l) hQ T
      (fun i _=>hlevels i) e f k.firstSlot k.secondSlot hp hj
    have hmark := k.indices e.depth f.depth r l hk
    dsimp only at H
    rw [hmark.1,hmark.2,nativeStreamingPairObservationIndex_level,
      nativeStreamingPairObservationIndex_second_level] at H
    simpa only [cavityGeneratedRawCrossObservationClock,cavityGeneratedRawCrossObservationTree,
      cavityGeneratedRawCrossSubdivision,cavityGeneratedRawCrossObservationFirst,
      cavityGeneratedRawCrossObservationSecond,cavityGeneratedRawCrossOrigin,nativeStreamingOriginCommonClock,
      hmark.1,hmark.2] using H

end QuantitativeFollowup
