module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossVertexPatternsConstruction
public import FourPapersCommon.FiniteCascadeLinearCrossGeometry

@[expose] public section

/-! The two new marks are literal terminal leaves of the constructed
double graft. Its terminal projection retains every original spin and
the genuine common level of the two independently continued leaves. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {j n : ℕ}

def nativeStreamingGeneratedCrossVertexTerminalProjection {S : Type}
    {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (σ : TerminalSpins S (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    TerminalSpins S T × (S×S) :=
  let z := nativeStreamingGeneratedVertexTerminalProjection .single
    (finiteCascadeContinuationVertexEmbed observationLinearTree v w) σ
  let y := nativeStreamingGeneratedVertexTerminalProjection .single v z.1
  (y.1,(y.2,z.2))

theorem nativeStreamingGeneratedCrossVertexTerminalProjection_record {E S : Type}
    {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    nativeStreamingGeneratedCrossVertexTerminalProjection v w (finiteCascadeRecordTerminalSpins _ z)=
      (finiteCascadeRecordTerminalSpins T
        (finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z).1,
        (finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z).2) := by
  let t := finiteCascadeContinuationVertexEmbed observationLinearTree v w
  let e := finiteCascadeContinuationExtract observationLinearTree observationLinearSpin t z
  have h1 : nativeStreamingGeneratedVertexTerminalProjection .single t
      (finiteCascadeRecordTerminalSpins _ z)=
      (finiteCascadeRecordTerminalSpins (finiteCascadeContinuationGraft observationLinearTree v) e.1,e.2) :=
    nativeStreamingGeneratedVertexTerminalProjection_record .single t z
  have h2 : nativeStreamingGeneratedVertexTerminalProjection .single v
      (finiteCascadeRecordTerminalSpins (finiteCascadeContinuationGraft observationLinearTree v) e.1)=
      (finiteCascadeRecordTerminalSpins T
        (finiteCascadeContinuationExtract observationLinearTree observationLinearSpin v e.1).1,
        (finiteCascadeContinuationExtract observationLinearTree observationLinearSpin v e.1).2) :=
    nativeStreamingGeneratedVertexTerminalProjection_record .single v e.1
  exact (congrArg (fun c : TerminalSpins S (finiteCascadeContinuationGraft observationLinearTree v) × S =>
      let y := nativeStreamingGeneratedVertexTerminalProjection .single v c.1
      (y.1,(y.2,c.2))) h1).trans
    (congrArg (fun c : TerminalSpins S T × S => (c.1,(c.2,e.2))) h2)

theorem nativeStreamingGeneratedCrossVertexTerminalProjection_old_leaf {E S : Type}
    {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) (i : ObservationLeaf T)
    (z : Records E S (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    observationTerminalSpin T i
      (nativeStreamingGeneratedCrossVertexTerminalProjection v w (finiteCascadeRecordTerminalSpins _ z)).1=
        observationLeafSpin _ (finiteCascadeLinearCrossOldLeaf v w i) z := by
  rw [nativeStreamingGeneratedCrossVertexTerminalProjection_record,observationTerminalSpin_record,
    finiteCascadeLinearCrossOldLeaf_spin]

theorem nativeStreamingGeneratedCrossVertexTerminalProjection_first_leaf {E S : Type}
    {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    (nativeStreamingGeneratedCrossVertexTerminalProjection v w (finiteCascadeRecordTerminalSpins _ z)).2.1=
      observationLeafSpin _ (finiteCascadeLinearCrossFirstLeaf v w) z := by
  rw [nativeStreamingGeneratedCrossVertexTerminalProjection_record,finiteCascadeLinearCrossFirstLeaf_spin]

theorem nativeStreamingGeneratedCrossVertexTerminalProjection_second_leaf {E S : Type}
    {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    (nativeStreamingGeneratedCrossVertexTerminalProjection v w (finiteCascadeRecordTerminalSpins _ z)).2.2=
      observationLeafSpin _ (finiteCascadeLinearCrossSecondLeaf v w) z := by
  rw [nativeStreamingGeneratedCrossVertexTerminalProjection_record,finiteCascadeLinearCrossSecondLeaf_spin]

theorem nativeStreamingGeneratedCrossVertexTerminalProjection_defect {E : Type}
    {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (q : ℕ → Paper.Overlap)
    (z : Records E (Configuration (n+1)) (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    cavitySpinOverlapDefect n (q (finiteCascadeCommonPathDepth T v w))
      (nativeStreamingGeneratedCrossVertexTerminalProjection v w (finiteCascadeRecordTerminalSpins _ z)).2.1
      (nativeStreamingGeneratedCrossVertexTerminalProjection v w (finiteCascadeRecordTerminalSpins _ z)).2.2=
    cavitySpinOverlapDefect n
      (q (observationCommonLevel _ (finiteCascadeLinearCrossFirstLeaf v w)
        (finiteCascadeLinearCrossSecondLeaf v w)))
      (observationLeafSpin _ (finiteCascadeLinearCrossFirstLeaf v w) z)
      (observationLeafSpin _ (finiteCascadeLinearCrossSecondLeaf v w) z) := by
  rw [finiteCascadeLinearCrossFresh_commonLevel,
    nativeStreamingGeneratedCrossVertexTerminalProjection_first_leaf,
    nativeStreamingGeneratedCrossVertexTerminalProjection_second_leaf]

end QuantitativeFollowup
