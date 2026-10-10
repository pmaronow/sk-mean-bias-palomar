module
public import FourPapersCommon.FiniteObservationRefinementTransport
public import FourPapersCommon.FiniteCascadeTerminalSampleEquiv
public import FourPapersCommon.FiniteObservationLeafGeometry

@[expose] public section

/-! Literal terminal-spin observables and their preservation when extra
observation times are inserted. Added fields never alter terminal marks. -/
noncomputable section
open MeasureTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy

@[reducible] def terminalSpinTopologicalSpace (S : Type) [TopologicalSpace S] :
    {j : ℕ}→(T : FiniteTerminalGenealogy j)→TopologicalSpace (TerminalSpins S T)
  | _, .leaf => inferInstanceAs (TopologicalSpace S)
  | _, .advance T => terminalSpinTopologicalSpace S T
  | _, .fork T U => @instTopologicalSpaceProd _ _
      (terminalSpinTopologicalSpace S T) (terminalSpinTopologicalSpace S U)

instance instTopologicalTerminalSpins (S : Type) [TopologicalSpace S] {j : ℕ}
    (T : FiniteTerminalGenealogy j) : TopologicalSpace (TerminalSpins S T):=
  terminalSpinTopologicalSpace S T

instance instDiscreteTerminalSpins (S : Type) [TopologicalSpace S] [DiscreteTopology S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) : DiscreteTopology (TerminalSpins S T) := by
  induction T with
  | leaf => exact inferInstanceAs (DiscreteTopology S)
  | advance T ih => exact ih
  | fork T U ihT ihU =>
    haveI:=ihT
    haveI:=ihU
    change DiscreteTopology (TerminalSpins S T×TerminalSpins S U)
    infer_instance

@[reducible] def observationTerminalSpin {S : Type} : {j : ℕ}→(T : FiniteTerminalGenealogy j)→
    ObservationLeaf T→TerminalSpins S T→S
  | _, .leaf => fun _=>id
  | _, .advance T => observationTerminalSpin T
  | _, .fork T U => fun i σ=>Sum.elim (fun l=>observationTerminalSpin T l σ.1)
      (fun r=>observationTerminalSpin U r σ.2) i

theorem observationTerminalSpin_record {E S : Type} {j : ℕ} (T : FiniteTerminalGenealogy j)
    (i : ObservationLeaf T) (z : Records E S T) :
    observationTerminalSpin T i (finiteCascadeRecordTerminalSpins T z)=observationLeafSpin T i z := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih i z.2
  | fork T U ihT ihU => cases i with
    | inl i => exact ihT i z.1
    | inr i => exact ihU i z.2

@[reducible] def observationUnitRecord {S : Type} : {j : ℕ}→(T : FiniteTerminalGenealogy j)→
    TerminalSpins S T→Records Unit S T
  | _, .leaf => id
  | _, .advance T => fun σ=>((),observationUnitRecord T σ)
  | _, .fork T U => Prod.map (observationUnitRecord T) (observationUnitRecord U)

theorem observationTreeMap_unit_eq_record {E S : Type} {j : ℕ}
    (T : FiniteTerminalGenealogy j) (z : Records E S T) :
    observationTreeMap (fun _ : E=>()) T z=observationUnitRecord T (finiteCascadeRecordTerminalSpins T z) := by
  induction T with
  | leaf => rfl
  | advance T ih => exact congrArg (Prod.mk ()) (ih z.2)
  | fork T U ihT ihU => exact congrArg₂ Prod.mk (ihT z.1) (ihU z.2)

theorem finiteCascadeRecordTerminalSpins_treeMap {E F S : Type} (f : E→F) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (z : Records E S T) :
    finiteCascadeRecordTerminalSpins T (observationTreeMap f T z)=finiteCascadeRecordTerminalSpins T z := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih z.2
  | fork T U ihT ihU => exact congrArg₂ Prod.mk (ihT z.1) (ihU z.2)

theorem continuous_finiteCascadeRecordTerminalSpins {E S : Type} [TopologicalSpace E]
    [TopologicalSpace S] {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Continuous (finiteCascadeRecordTerminalSpins (E:=E) (S:=S) T) := by
  induction T with
  | leaf => exact continuous_id
  | advance T ih => exact ih.comp continuous_snd
  | fork T U ihT ihU => exact ihT.prodMap ihU

def observationRefinementTerminalProject {S : Type} (d : ℕ→ℕ) {j l : ℕ}
    (T : FiniteTerminalGenealogy j) (h : observationRefinementDepth d j=l) :
    TerminalSpins S (observationTreeDepthCast h (observationRefineTree d T))→TerminalSpins S T :=
  fun σ=>finiteCascadeRecordTerminalSpins T
    (observationRefinementDepthProject d T h (observationUnitRecord _ σ))

theorem observationRefinementTerminalProject_record {E S : Type} (d : ℕ→ℕ) {j l : ℕ}
    (T : FiniteTerminalGenealogy j) (h : observationRefinementDepth d j=l)
    (z : Records E S (observationTreeDepthCast h (observationRefineTree d T))) :
    observationRefinementTerminalProject d T h (finiteCascadeRecordTerminalSpins _ z)=
      finiteCascadeRecordTerminalSpins T (observationRefinementDepthProject d T h z) := by
  unfold observationRefinementTerminalProject
  rw [←observationTreeMap_unit_eq_record]
  have hc:=congrFun (observationRefinementDepthProject_map (S:=S) (fun _ : E=>()) d T h) z
  change observationTreeMap (fun _ : E=>()) T (observationRefinementDepthProject d T h z)=
    observationRefinementDepthProject d T h (observationTreeMap (fun _ : E=>()) _ z) at hc
  rw [←hc,finiteCascadeRecordTerminalSpins_treeMap]

theorem leafCount_observationTreePad {j : ℕ} (T : FiniteTerminalGenealogy j) (d : ℕ) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (observationTreePad T d))=
      FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem leafCount_observationRefineTree (d : ℕ→ℕ) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (observationRefineTree d T))=
      FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
  induction T with
  | leaf => rfl
  | advance T ih => exact (leafCount_observationTreePad _ _).trans ih
  | fork T U ihT ihU =>
    simp only [observationRefineTree,asGenealogy,FiniteCascadeGenealogy.leafCount]
    rw [ihT,ihU]

theorem leafCount_observationRefinementDepthCast (d : ℕ→ℕ) {j l : ℕ}
    (T : FiniteTerminalGenealogy j) (h : observationRefinementDepth d j=l) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (observationTreeDepthCast h (observationRefineTree d T)))=
      FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
  subst l
  exact leafCount_observationRefineTree d T

end FourPapersCommon
