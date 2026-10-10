module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawProperties
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossEdgePatternsClocks
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSelectedCrossPatternMomentsLaw

@[expose] public section

/-! Both cross locations are decoded on the original observed tree.  The
observation mesh inserts no point for two vertices, one point for a single
edge, and two fixed slots for two edges.  Equal marks retain independent
terminal spins at their genuinely shared observation vertex. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {J n : ℕ}

abbrev CavityGeneratedRawCrossSite (T : FiniteTerminalGenealogy J) :=
  FiniteCascadeRecordVertex T ⊕ NativeStreamingEdge T

def cavityGeneratedRawCrossSite (T : FiniteTerminalGenealogy J) :
    CavityGeneratedObservedRawOriginChart T → CavityGeneratedRawCrossSite T
  | .inl i => .inl ((cavityGeneratedOriginForkVertices T).get i)
  | .inr (.inl i) => .inr ((cavityGeneratedOriginEdges T).get i)
  | .inr (.inr _) => .inl (.root T)

def cavityGeneratedRawCrossOrigin (T : FiniteTerminalGenealogy J)
    (s : CavityGeneratedRawCrossSite T) (r : Paper.Overlap) : NativeStreamingOrigin T :=
  match s with
  | .inl v => .vertex v
  | .inr e => .edge e r

def cavityGeneratedRawCrossCell (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (s : CavityGeneratedRawCrossSite T)
    (r : Paper.Overlap) : Prop :=
  match s with
  | .inl _ => True
  | .inr e => q (e.depth+1)≤r ∧ r≤q e.depth

def cavityGeneratedRawCrossChartHolds (T : FiniteTerminalGenealogy J)
    (s t : CavityGeneratedRawCrossSite T) (k : NativeStreamingGeneratedCrossEdgeChart)
    (r l : Paper.Overlap) : Prop :=
  match s,t with
  | .inr e,.inr f => k.Holds e.depth f.depth r l
  | _,_ => True

def cavityGeneratedRawCrossSubdivision (T : FiniteTerminalGenealogy J)
    (s t : CavityGeneratedRawCrossSite T) : ℕ → ℕ :=
  match s,t with
  | .inl _,.inl _ => fun _=>0
  | .inr e,.inl _ => nativeStreamingEdgeSubdivision e.depth
  | .inl _,.inr f => nativeStreamingEdgeSubdivision f.depth
  | .inr _,.inr _ => nativeStreamingPairObservationSubdivision

def cavityGeneratedRawCrossObservationClock (T : FiniteTerminalGenealogy J)
    (s t : CavityGeneratedRawCrossSite T) (q : ℕ → Paper.Overlap)
    (r l : Paper.Overlap) : ℕ → Paper.Overlap :=
  match s,t with
  | .inl _,.inl _ => q
  | .inr e,.inl _ => nativeStreamingEdgeSchedule q e.depth r
  | .inl _,.inr f => nativeStreamingEdgeSchedule q f.depth l
  | .inr e,.inr f => nativeStreamingPairObservationSchedule q e.depth f.depth r l

def cavityGeneratedRawCrossObservationTree (T : FiniteTerminalGenealogy J)
    (s t : CavityGeneratedRawCrossSite T) :
    FiniteTerminalGenealogy (observationRefinementDepth (cavityGeneratedRawCrossSubdivision T s t) J) :=
  observationRefineTree (cavityGeneratedRawCrossSubdivision T s t) T

def cavityGeneratedRawCrossObservationFirst (T : FiniteTerminalGenealogy J)
    (s t : CavityGeneratedRawCrossSite T) (k : NativeStreamingGeneratedCrossEdgeChart) :
    FiniteCascadeRecordVertex (cavityGeneratedRawCrossObservationTree T s t) :=
  match s,t with
  | .inl v,.inl _ => nativeStreamingRefinementVertexEmbed (fun _=>0) T v
  | .inr e,.inl _ => nativeStreamingEdgeSelectedVertex (nativeStreamingEdgeSubdivision e.depth) e 0
  | .inl v,.inr f => nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision f.depth) T v
  | .inr e,.inr _ => nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e k.firstSlot

def cavityGeneratedRawCrossObservationSecond (T : FiniteTerminalGenealogy J)
    (s t : CavityGeneratedRawCrossSite T) (k : NativeStreamingGeneratedCrossEdgeChart) :
    FiniteCascadeRecordVertex (cavityGeneratedRawCrossObservationTree T s t) :=
  match s,t with
  | .inl _,.inl w => nativeStreamingRefinementVertexEmbed (fun _=>0) T w
  | .inr e,.inl w => nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T w
  | .inl _,.inr f => nativeStreamingEdgeSelectedVertex (nativeStreamingEdgeSubdivision f.depth) f 0
  | .inr _,.inr f => nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision f k.secondSlot

private theorem rawCross_zero_refinementDepth (i : ℕ) :
    observationRefinementDepth (fun _=>0) i=i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [observationRefinementDepth,ih, Nat.add_zero]

theorem cavityGeneratedRawCrossObservation_refinement
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (q : ℕ → Paper.Overlap) (r l : Paper.Overlap) (i : ℕ) :
    cavityGeneratedRawCrossObservationClock T s t q r l
      (observationRefinementDepth (cavityGeneratedRawCrossSubdivision T s t) i)=q i := by
  rcases s with v | e <;> rcases t with w | f
  · change q (observationRefinementDepth (fun _=>0) i)=q i
    rw [rawCross_zero_refinementDepth]
  · exact nativeStreamingEdgeSchedule_refinement q f.depth l i
  · exact nativeStreamingEdgeSchedule_refinement q e.depth r i
  · exact nativeStreamingPairObservationSchedule_refinement q e.depth f.depth r l i

theorem cavityGeneratedRawCrossObservation_antitone
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell q T s r)
    (hl : cavityGeneratedRawCrossCell q T t l) :
    Antitone (cavityGeneratedRawCrossObservationClock T s t q r l) := by
  rcases s with v | e <;> rcases t with w | f
  · exact hq
  · exact nativeStreamingEdgeSchedule_antitone q hq f.depth l hl
  · exact nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
  · exact nativeStreamingPairObservationSchedule_antitone q hq e.depth f.depth r l hr hl

theorem cavityGeneratedRawCrossObservation_first_clock
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart) (q : ℕ → Paper.Overlap)
    (r l : Paper.Overlap) (hk : cavityGeneratedRawCrossChartHolds T s t k r l) :
    cavityGeneratedRawCrossObservationClock T s t q r l
      (cavityGeneratedRawCrossObservationFirst T s t k).depth =
      nativeStreamingOriginLevel q (cavityGeneratedRawCrossOrigin T s r) := by
  rcases s with v | e <;> rcases t with w | f
  · change q (nativeStreamingRefinementVertexEmbed (fun _=>0) T v).depth=q v.depth
    rw [nativeStreamingRefinementVertexEmbed_depth,rawCross_zero_refinementDepth]
  · change nativeStreamingEdgeSchedule q f.depth l
      (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision f.depth) T v).depth=q v.depth
    rw [nativeStreamingRefinementVertexEmbed_depth,nativeStreamingEdgeSchedule_refinement]
  · have hp : 0<nativeStreamingEdgeSubdivision e.depth e.depth := by
      simp [nativeStreamingEdgeSubdivision]
    change nativeStreamingEdgeSchedule q e.depth r
      (nativeStreamingEdgeSelectedVertex (nativeStreamingEdgeSubdivision e.depth) e 0).depth=r
    rw [nativeStreamingEdgeSelectedVertex_depth _ e 0 hp]
    simp [nativeStreamingEdgeSubdivision_depth,nativeStreamingEdgeSchedule]
  · have hp : k.firstSlot<nativeStreamingPairObservationSubdivision e.depth := k.firstSlot_lt
    change nativeStreamingPairObservationSchedule q e.depth f.depth r l
      (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e k.firstSlot).depth=r
    rw [nativeStreamingEdgeSelectedVertex_depth _ e _ hp,(k.indices e.depth f.depth r l hk).1]
    exact nativeStreamingPairObservationIndex_level q e.depth f.depth r l

theorem cavityGeneratedRawCrossObservation_second_clock
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart) (q : ℕ → Paper.Overlap)
    (r l : Paper.Overlap) (hk : cavityGeneratedRawCrossChartHolds T s t k r l) :
    cavityGeneratedRawCrossObservationClock T s t q r l
      (cavityGeneratedRawCrossObservationSecond T s t k).depth =
      nativeStreamingOriginLevel q (cavityGeneratedRawCrossOrigin T t l) := by
  rcases s with v | e <;> rcases t with w | f
  · change q (nativeStreamingRefinementVertexEmbed (fun _=>0) T w).depth=q w.depth
    rw [nativeStreamingRefinementVertexEmbed_depth,rawCross_zero_refinementDepth]
  · have hp : 0<nativeStreamingEdgeSubdivision f.depth f.depth := by
      simp [nativeStreamingEdgeSubdivision]
    change nativeStreamingEdgeSchedule q f.depth l
      (nativeStreamingEdgeSelectedVertex (nativeStreamingEdgeSubdivision f.depth) f 0).depth=l
    rw [nativeStreamingEdgeSelectedVertex_depth _ f 0 hp]
    simp [nativeStreamingEdgeSubdivision_depth,nativeStreamingEdgeSchedule]
  · change nativeStreamingEdgeSchedule q e.depth r
      (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T w).depth=q w.depth
    rw [nativeStreamingRefinementVertexEmbed_depth,nativeStreamingEdgeSchedule_refinement]
  · have hp : k.secondSlot<nativeStreamingPairObservationSubdivision f.depth := k.secondSlot_lt
    change nativeStreamingPairObservationSchedule q e.depth f.depth r l
      (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision f k.secondSlot).depth=l
    rw [nativeStreamingEdgeSelectedVertex_depth _ f _ hp,(k.indices e.depth f.depth r l hk).2]
    exact nativeStreamingPairObservationIndex_second_level q e.depth f.depth r l

/-- Exact full old record and ordered pair law, with both locations still original. -/
theorem cavityGeneratedRawCrossObservation_full_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart) (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (hzero : q 0=1) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell q T s r)
    (hl : cavityGeneratedRawCrossCell q T t l)
    (hk : cavityGeneratedRawCrossChartHolds T s t k r l) :
    (nativeStreamingCrossVertexLaw D μ a (cavityGeneratedRawCrossObservationClock T s t q r l)
      (cavityGeneratedRawCrossObservationTree T s t)
      (cavityGeneratedRawCrossObservationFirst T s t k)
      (cavityGeneratedRawCrossObservationSecond T s t k)).map
        (fun z=>((z.1.1,observationRefinementProject
          (cavityGeneratedRawCrossSubdivision T s t) T z.1.2),z.2))=
      (nativeStreamingOriginCrossProbability D μ a q T
        (cavityGeneratedRawCrossOrigin T s r) (cavityGeneratedRawCrossOrigin T t l) : Measure _) := by
  have hQ := cavityGeneratedRawCrossObservation_antitone T s t q hq r l hr hl
  have hlevels := cavityGeneratedRawCrossObservation_refinement T s t q r l
  rcases s with v | e <;> rcases t with w | f
  · change (nativeStreamingCrossVertexLaw D μ a q (observationRefineTree (fun _=>0) T)
      (nativeStreamingRefinementVertexEmbed (fun _=>0) T v)
      (nativeStreamingRefinementVertexEmbed (fun _=>0) T w)).map _=
      (nativeStreamingCrossVertexProbability D μ a q T v w : Measure ((AnisotropicObservationState n × Records (AnisotropicObservationState n) (Configuration n) T) × (Configuration n × Configuration n)))
    rw [nativeStreamingCrossVertexProbability_eq_law D μ a q hq hzero]
    exact nativeStreamingCrossVertexLaw_refinement D μ a q q (fun _=>0) hq hlevels T v w
  · have hp : 0<nativeStreamingEdgeSubdivision f.depth f.depth := by simp [nativeStreamingEdgeSubdivision]
    have H := nativeStreamingSelectedCrossLaw_VE_projection_eq_origin D μ a q _ _ hQ hlevels hzero T f 0 hp v
    have hm : nativeStreamingEdgeSchedule q f.depth l
        (observationRefinementDepth (nativeStreamingEdgeSubdivision f.depth) f.depth+0+1)=l := by
      simp [nativeStreamingEdgeSubdivision_depth,nativeStreamingEdgeSchedule]
    dsimp only [cavityGeneratedRawCrossObservationClock,cavityGeneratedRawCrossSubdivision] at H
    rw [hm] at H
    exact H
  · have hp : 0<nativeStreamingEdgeSubdivision e.depth e.depth := by simp [nativeStreamingEdgeSubdivision]
    have H := nativeStreamingSelectedCrossLaw_EV_projection_eq_origin D μ a q _ _ hQ hlevels hzero T e 0 hp w
    have hm : nativeStreamingEdgeSchedule q e.depth r
        (observationRefinementDepth (nativeStreamingEdgeSubdivision e.depth) e.depth+0+1)=r := by
      simp [nativeStreamingEdgeSubdivision_depth,nativeStreamingEdgeSchedule]
    dsimp only [cavityGeneratedRawCrossObservationClock,cavityGeneratedRawCrossSubdivision] at H
    rw [hm] at H
    exact H
  · have hp : k.firstSlot<nativeStreamingPairObservationSubdivision e.depth := k.firstSlot_lt
    have hj : k.secondSlot<nativeStreamingPairObservationSubdivision f.depth := k.secondSlot_lt
    have H := nativeStreamingSelectedCrossLaw_EE_projection_eq_origin D μ a q _ _ hQ hlevels hzero T e f k.firstSlot k.secondSlot hp hj
    have hmark := k.indices e.depth f.depth r l hk
    dsimp only [cavityGeneratedRawCrossObservationClock,cavityGeneratedRawCrossSubdivision] at H
    dsimp only [cavityGeneratedRawCrossObservationFirst,cavityGeneratedRawCrossObservationSecond] at ⊢
    rw [hmark.1,hmark.2] at H ⊢
    rw [nativeStreamingPairObservationIndex_level,
      nativeStreamingPairObservationIndex_second_level] at H
    exact H

end QuantitativeFollowup
