module
public import QuantitativeFollowup.FollowupCavityGeneratedRawCrossPhysical
public import QuantitativeFollowup.FollowupCavityGeneratedRawCrossComponent

@[expose] public section

/-! The two newly attached leaves and every old leaf are literal leaves
of the raw successor. Their terminal spins and physical pair clocks are
preserved pointwise, including diagonal old pairs and coincident marks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {J m n : ℕ}

def cavityGeneratedRawCrossOldLeaf (T : FiniteTerminalGenealogy J)
    (s t : CavityGeneratedRawCrossSite T) (k : NativeStreamingGeneratedCrossEdgeChart)
    (i : ObservationLeaf T) : ObservationLeaf (cavityGeneratedRawCrossTree T s t k) :=
  finiteCascadeLinearCrossOldLeaf (cavityGeneratedRawCrossObservationFirst T s t k)
    (cavityGeneratedRawCrossObservationSecond T s t k)
    (observationRefinementLeafEmbed (cavityGeneratedRawCrossSubdivision T s t) T i)

def cavityGeneratedRawCrossFirstLeaf (T : FiniteTerminalGenealogy J)
    (s t : CavityGeneratedRawCrossSite T) (k : NativeStreamingGeneratedCrossEdgeChart) :
    ObservationLeaf (cavityGeneratedRawCrossTree T s t k) :=
  finiteCascadeLinearCrossFirstLeaf (cavityGeneratedRawCrossObservationFirst T s t k)
    (cavityGeneratedRawCrossObservationSecond T s t k)

def cavityGeneratedRawCrossSecondLeaf (T : FiniteTerminalGenealogy J)
    (s t : CavityGeneratedRawCrossSite T) (k : NativeStreamingGeneratedCrossEdgeChart) :
    ObservationLeaf (cavityGeneratedRawCrossTree T s t k) :=
  finiteCascadeLinearCrossSecondLeaf (cavityGeneratedRawCrossObservationFirst T s t k)
    (cavityGeneratedRawCrossObservationSecond T s t k)

theorem cavityGeneratedRawCross_old_spin {E S : Type}
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart) (i : ObservationLeaf T)
    (z : E × Records E S (cavityGeneratedRawCrossTree T s t k)) :
    observationTerminalSpin T i (cavityGeneratedRawCrossTerminalProjection T s t k
      (finiteCascadeRecordTerminalSpins _ z.2)).1=
      observationLeafSpin _ (cavityGeneratedRawCrossOldLeaf T s t k i) z.2 := by
  unfold cavityGeneratedRawCrossTerminalProjection
  rw [observationRefinementTerminalProject_leaf]
  exact nativeStreamingGeneratedCrossVertexTerminalProjection_old_leaf _ _ _ z.2

theorem cavityGeneratedRawCross_old_terminal_spin {S : Type}
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart) (i : ObservationLeaf T)
    (σ : TerminalSpins S (cavityGeneratedRawCrossTree T s t k)) :
    observationTerminalSpin T i (cavityGeneratedRawCrossTerminalProjection T s t k σ).1=
      observationTerminalSpin _ (cavityGeneratedRawCrossOldLeaf T s t k i) σ := by
  have H := cavityGeneratedRawCross_old_spin T s t k i
    ((),observationUnitRecord (cavityGeneratedRawCrossTree T s t k) σ)
  simpa only [←observationTerminalSpin_record,finiteCascadeRecordTerminalSpins_unit] using H

theorem cavityGeneratedRawCross_fresh_spins {E S : Type}
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (z : E × Records E S (cavityGeneratedRawCrossTree T s t k)) :
    (cavityGeneratedRawCrossTerminalProjection T s t k (finiteCascadeRecordTerminalSpins _ z.2)).2=
      (observationLeafSpin _ (cavityGeneratedRawCrossFirstLeaf T s t k) z.2,
        observationLeafSpin _ (cavityGeneratedRawCrossSecondLeaf T s t k) z.2) :=
  Prod.ext (nativeStreamingGeneratedCrossVertexTerminalProjection_first_leaf _ _ z.2)
    (nativeStreamingGeneratedCrossVertexTerminalProjection_second_leaf _ _ z.2)

theorem cavityGeneratedRawCross_fresh_terminal_spins {S : Type}
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (σ : TerminalSpins S (cavityGeneratedRawCrossTree T s t k)) :
    (cavityGeneratedRawCrossTerminalProjection T s t k σ).2=
      (observationTerminalSpin _ (cavityGeneratedRawCrossFirstLeaf T s t k) σ,
        observationTerminalSpin _ (cavityGeneratedRawCrossSecondLeaf T s t k) σ) := by
  have H := cavityGeneratedRawCross_fresh_spins T s t k
    ((),observationUnitRecord (cavityGeneratedRawCrossTree T s t k) σ)
  simpa only [←observationTerminalSpin_record,finiteCascadeRecordTerminalSpins_unit] using H

theorem cavityGeneratedRawCross_old_pair_clock
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart) (q : ℕ → Paper.Overlap) (r l : Paper.Overlap)
    (i j : ObservationLeaf T) :
    cavityGeneratedRawCrossObservationClock T s t q r l
      (observationCommonLevel _ (cavityGeneratedRawCrossOldLeaf T s t k i)
        (cavityGeneratedRawCrossOldLeaf T s t k j))=q (observationCommonLevel T i j) := by
  unfold cavityGeneratedRawCrossOldLeaf cavityGeneratedRawCrossTree cavityGeneratedRawCrossObservationTree
  erw [finiteCascadeLinearCrossOldLeaf_commonLevel,observationRefinementLeafEmbed_commonLevel]
  exact cavityGeneratedRawCrossObservation_refinement T s t q r l _

theorem cavityGeneratedRawCross_fresh_pair_clock
    (T : FiniteTerminalGenealogy J) (s t : CavityGeneratedRawCrossSite T)
    (k : NativeStreamingGeneratedCrossEdgeChart) (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell q T s r)
    (hl : cavityGeneratedRawCrossCell q T t l)
    (hk : cavityGeneratedRawCrossChartHolds T s t k r l) :
    cavityGeneratedRawCrossObservationClock T s t q r l
      (observationCommonLevel _ (cavityGeneratedRawCrossFirstLeaf T s t k)
        (cavityGeneratedRawCrossSecondLeaf T s t k))=
      nativeStreamingOriginCommonClock q T
        (cavityGeneratedRawCrossOrigin T s r) (cavityGeneratedRawCrossOrigin T t l) := by
  unfold cavityGeneratedRawCrossFirstLeaf cavityGeneratedRawCrossSecondLeaf cavityGeneratedRawCrossTree
  rw [finiteCascadeLinearCrossFresh_commonLevel]
  exact cavityGeneratedRawCrossObservation_common_clock T s t k q hq r l hr hl hk

theorem cavityGeneratedObservedRawCross_old_pair_defect
    (U : CavityGeneratedObservedRawComponent m) (s t : CavityGeneratedRawCrossSite U.tree)
    (k : NativeStreamingGeneratedCrossEdgeChart) (h : CavityGeneratedHistory Paper.Overlap m)
    (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell (U.clock h) U.tree s r)
    (hl : cavityGeneratedRawCrossCell (U.clock h) U.tree t l)
    (i j : ObservationLeaf U.tree)
    (σ : TerminalSpins (Configuration (n+1)) (cavityGeneratedRawCrossTree U.tree s t k)) :
    cavitySpinOverlapDefect n (U.clock h (observationCommonLevel U.tree i j))
      (observationTerminalSpin U.tree i (cavityGeneratedRawCrossTerminalProjection U.tree s t k σ).1)
      (observationTerminalSpin U.tree j (cavityGeneratedRawCrossTerminalProjection U.tree s t k σ).1)=
    cavitySpinOverlapDefect n
      ((cavityGeneratedObservedRawCrossComponent U s t k).clock (cavityGeneratedRawCrossAppend h r l)
        (observationCommonLevel _ (cavityGeneratedRawCrossOldLeaf U.tree s t k i)
          (cavityGeneratedRawCrossOldLeaf U.tree s t k j)))
      (observationTerminalSpin _ (cavityGeneratedRawCrossOldLeaf U.tree s t k i) σ)
      (observationTerminalSpin _ (cavityGeneratedRawCrossOldLeaf U.tree s t k j) σ) := by
  rw [cavityGeneratedObservedRawCrossComponent_clock_append U s t k h r l hr hl,
    cavityGeneratedRawCross_old_pair_clock,cavityGeneratedRawCross_old_terminal_spin,
    cavityGeneratedRawCross_old_terminal_spin]

theorem cavityGeneratedObservedRawCross_fresh_pair_defect
    (U : CavityGeneratedObservedRawComponent m) (s t : CavityGeneratedRawCrossSite U.tree)
    (k : NativeStreamingGeneratedCrossEdgeChart) (h : CavityGeneratedHistory Paper.Overlap m)
    (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell (U.clock h) U.tree s r)
    (hl : cavityGeneratedRawCrossCell (U.clock h) U.tree t l)
    (hk : cavityGeneratedRawCrossChartHolds U.tree s t k r l)
    (σ : TerminalSpins (Configuration (n+1)) (cavityGeneratedRawCrossTree U.tree s t k)) :
    cavitySpinOverlapDefect n
      (nativeStreamingOriginCommonClock (U.clock h) U.tree
        (cavityGeneratedRawCrossOrigin U.tree s r) (cavityGeneratedRawCrossOrigin U.tree t l))
      (cavityGeneratedRawCrossTerminalProjection U.tree s t k σ).2.1
      (cavityGeneratedRawCrossTerminalProjection U.tree s t k σ).2.2=
    cavitySpinOverlapDefect n
      ((cavityGeneratedObservedRawCrossComponent U s t k).clock (cavityGeneratedRawCrossAppend h r l)
        (observationCommonLevel _ (cavityGeneratedRawCrossFirstLeaf U.tree s t k)
          (cavityGeneratedRawCrossSecondLeaf U.tree s t k)))
      (observationTerminalSpin _ (cavityGeneratedRawCrossFirstLeaf U.tree s t k) σ)
      (observationTerminalSpin _ (cavityGeneratedRawCrossSecondLeaf U.tree s t k) σ) := by
  rw [cavityGeneratedObservedRawCrossComponent_clock_append U s t k h r l hr hl,
    cavityGeneratedRawCross_fresh_pair_clock U.tree s t k (U.clock h) (U.clock_antitone h) r l hr hl hk]
  have hp := cavityGeneratedRawCross_fresh_terminal_spins U.tree s t k σ
  exact congrArg₂ (cavitySpinOverlapDefect n _)
    (congrArg Prod.fst hp) (congrArg Prod.snd hp)

end QuantitativeFollowup
