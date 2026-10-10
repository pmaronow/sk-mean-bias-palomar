module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexPatternsConstruction
public import FourPapersCommon.FiniteCascadeContinuationLeafGeometry
public import FourPapersCommon.FiniteCascadeFuturePairSpins

@[expose] public section

/-! A continuation graft has a literal terminal-spin projection retaining
all original spins and the new marks. The projection is proved on every
full record, with no conditional-law or marginal hypothesis. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def nativeStreamingGeneratedContinuationTerminalMap {S : Type}
    (U : (j : ℕ) → FiniteTerminalGenealogy j) :
    {j : ℕ} → {T : FiniteTerminalGenealogy j} → (v : FiniteCascadeRecordVertex T) →
      TerminalSpins S (finiteCascadeContinuationGraft U v) → TerminalSpins S T × TerminalSpins S (U v.depth)
  | _, _, .root _ => id
  | _, _, .child v => nativeStreamingGeneratedContinuationTerminalMap U v
  | _, _, .left v => fun σ =>
      (((nativeStreamingGeneratedContinuationTerminalMap U v σ.1).1,σ.2),
        (nativeStreamingGeneratedContinuationTerminalMap U v σ.1).2)
  | _, _, .right v => fun σ =>
      ((σ.1,(nativeStreamingGeneratedContinuationTerminalMap U v σ.2).1),
        (nativeStreamingGeneratedContinuationTerminalMap U v σ.2).2)

theorem nativeStreamingGeneratedContinuationTerminalMap_record {E S : Type}
    (U : (j : ℕ) → FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) (z : Records E S (finiteCascadeContinuationGraft U v)) :
    nativeStreamingGeneratedContinuationTerminalMap U v (finiteCascadeRecordTerminalSpins _ z) =
      (finiteCascadeRecordTerminalSpins T (finiteCascadeContinuationRecords U v z).1,
        finiteCascadeRecordTerminalSpins (U v.depth) (finiteCascadeContinuationRecords U v z).2) := by
  induction v with
  | root T => rfl
  | child v ih => exact ih z.2
  | left v ih =>
      change (((nativeStreamingGeneratedContinuationTerminalMap U v
        (finiteCascadeRecordTerminalSpins _ z.1)).1,finiteCascadeRecordTerminalSpins _ z.2),
        (nativeStreamingGeneratedContinuationTerminalMap U v (finiteCascadeRecordTerminalSpins _ z.1)).2)=_
      rw [ih z.1]
      rfl
  | right v ih =>
      change ((finiteCascadeRecordTerminalSpins _ z.1,(nativeStreamingGeneratedContinuationTerminalMap U v
        (finiteCascadeRecordTerminalSpins _ z.2)).1),
        (nativeStreamingGeneratedContinuationTerminalMap U v (finiteCascadeRecordTerminalSpins _ z.2)).2)=_
      rw [ih z.2]
      rfl

theorem nativeStreamingGeneratedLinearLeaf_spin {E S : Type} (j : ℕ)
    (z : Records E S (observationLinearTree j)) :
    observationLeafSpin (observationLinearTree j) (observationLinearLeaf j) z=observationLinearSpin j z := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih z.2

namespace NativeStreamingGeneratedVertexKind

@[reducible] def Mark (k : NativeStreamingGeneratedVertexKind) (S : Type) : Type :=
  match k with
  | .single => S
  | .current => S×S

instance markFintype (k : NativeStreamingGeneratedVertexKind) (S : Type) [Fintype S] : Fintype (k.Mark S) := by
  cases k <;> dsimp only [Mark] <;> infer_instance
instance markMeasurableSpace (k : NativeStreamingGeneratedVertexKind) (S : Type) [MeasurableSpace S] : MeasurableSpace (k.Mark S) := by
  cases k <;> dsimp only [Mark] <;> infer_instance
instance markMeasurableSingletonClass (k : NativeStreamingGeneratedVertexKind) (S : Type)
    [MeasurableSpace S] [MeasurableSingletonClass S] : MeasurableSingletonClass (k.Mark S) := by
  cases k <;> dsimp only [Mark] <;> infer_instance
instance markTopologicalSpace (k : NativeStreamingGeneratedVertexKind) (S : Type) [TopologicalSpace S] : TopologicalSpace (k.Mark S) := by
  cases k <;> dsimp only [Mark] <;> infer_instance
instance markDiscreteTopology (k : NativeStreamingGeneratedVertexKind) (S : Type)
    [TopologicalSpace S] [DiscreteTopology S] : DiscreteTopology (k.Mark S) := by
  cases k <;> dsimp only [Mark] <;> infer_instance
instance markBorelSpace (k : NativeStreamingGeneratedVertexKind) (S : Type)
    [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S] [SecondCountableTopology S] : BorelSpace (k.Mark S) := by
  cases k <;> dsimp only [Mark] <;> infer_instance
instance markSecondCountableTopology (k : NativeStreamingGeneratedVertexKind) (S : Type)
    [TopologicalSpace S] [SecondCountableTopology S] : SecondCountableTopology (k.Mark S) := by
  cases k <;> dsimp only [Mark] <;> infer_instance

def recordMark {E S : Type} : (k : NativeStreamingGeneratedVertexKind) → (j : ℕ) →
    Records E S (k.continuation j) → k.Mark S
  | .single => observationLinearSpin
  | .current => nativeStreamingCurrentPairExtract

def terminalMark {S : Type} : (k : NativeStreamingGeneratedVertexKind) → (j : ℕ) →
    TerminalSpins S (k.continuation j) → k.Mark S
  | .single => fun j => observationTerminalSpin (observationLinearTree j) (observationLinearLeaf j)
  | .current => fun j => Prod.map
      (observationTerminalSpin (observationLinearTree j) (observationLinearLeaf j))
      (observationTerminalSpin (observationLinearTree j) (observationLinearLeaf j))

theorem terminalMark_record {E S : Type} (k : NativeStreamingGeneratedVertexKind) (j : ℕ)
    (z : Records E S (k.continuation j)) :
    k.terminalMark j (finiteCascadeRecordTerminalSpins _ z)=k.recordMark j z := by
  cases k with
  | single => exact (observationTerminalSpin_record _ _ z).trans (nativeStreamingGeneratedLinearLeaf_spin j z)
  | current =>
      change (_,_) = (_, _)
      exact congrArg₂ Prod.mk
        ((observationTerminalSpin_record _ _ z.1).trans (nativeStreamingGeneratedLinearLeaf_spin j z.1))
        ((observationTerminalSpin_record _ _ z.2).trans (nativeStreamingGeneratedLinearLeaf_spin j z.2))

theorem recordMark_measurable {E S : Type} [MeasurableSpace E] [MeasurableSpace S]
    (k : NativeStreamingGeneratedVertexKind) (j : ℕ) : Measurable (k.recordMark (E:=E) (S:=S) j) := by
  cases k with
  | single => exact measurable_observationLinearSpin (E:=E) (S:=S) j
  | current => exact nativeStreamingCurrentPairExtract_measurable (E:=E) (S:=S) j

theorem recordMark_continuous {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (k : NativeStreamingGeneratedVertexKind) (j : ℕ) : Continuous (k.recordMark (E:=E) (S:=S) j) := by
  cases k with
  | single => exact nativeStreamingLinearSpin_continuous (E:=E) (S:=S) j
  | current => exact nativeStreamingCurrentPairExtract_continuous (E:=E) (S:=S) j

end NativeStreamingGeneratedVertexKind

def nativeStreamingGeneratedVertexTerminalProjection {S : Type}
    (k : NativeStreamingGeneratedVertexKind) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T)
    (σ : TerminalSpins S (finiteCascadeContinuationGraft k.continuation v)) :
    TerminalSpins S T × k.Mark S :=
  let z := nativeStreamingGeneratedContinuationTerminalMap k.continuation v σ
  (z.1,k.terminalMark v.depth z.2)

theorem nativeStreamingGeneratedVertexTerminalProjection_record {E S : Type}
    (k : NativeStreamingGeneratedVertexKind) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) (z : Records E S (finiteCascadeContinuationGraft k.continuation v)) :
    nativeStreamingGeneratedVertexTerminalProjection k v (finiteCascadeRecordTerminalSpins _ z) =
      (finiteCascadeRecordTerminalSpins T
        (finiteCascadeContinuationExtract k.continuation k.recordMark v z).1,
        (finiteCascadeContinuationExtract k.continuation k.recordMark v z).2) := by
  unfold nativeStreamingGeneratedVertexTerminalProjection
  rw [nativeStreamingGeneratedContinuationTerminalMap_record]
  dsimp only
  rw [
    NativeStreamingGeneratedVertexKind.terminalMark_record,finiteCascadeContinuationExtract_eq_records]

/-- Every original terminal spin is literally retained by the terminal projection. -/
theorem nativeStreamingGeneratedVertexTerminalProjection_old_leaf {E S : Type}
    (k : NativeStreamingGeneratedVertexKind) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) (i : ObservationLeaf T)
    (z : Records E S (finiteCascadeContinuationGraft k.continuation v)) :
    observationTerminalSpin T i
      (nativeStreamingGeneratedVertexTerminalProjection k v (finiteCascadeRecordTerminalSpins _ z)).1 =
      observationLeafSpin (finiteCascadeContinuationGraft k.continuation v)
        (finiteCascadeContinuationOldLeaf k.continuation v i) z := by
  rw [nativeStreamingGeneratedVertexTerminalProjection_record,
    finiteCascadeContinuationExtract_eq_records,observationTerminalSpin_record,
    finiteCascadeContinuationOldLeaf_spin]

end QuantitativeFollowup
