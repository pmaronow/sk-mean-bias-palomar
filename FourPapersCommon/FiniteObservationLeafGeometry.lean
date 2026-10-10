module
public import FourPapersCommon.FiniteObservationTreePairPruning
public import FourPapersCommon.FiniteCascadeTreePathCovariance
public import FourPapersCommon.FiniteObservationTreeTransport

@[expose] public section

/-! Terminal observation leaves have literal recorded terminal vertices;
their common-path depth is exactly their genealogical common level. -/
noncomputable section
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 500000

@[reducible] def observationLeafVertex : {j : ℕ}→(T : FiniteTerminalGenealogy j)→
    ObservationLeaf T→FiniteCascadeRecordVertex T
  | _, .leaf => fun _=>.root .leaf
  | _, .advance T => fun i=>.child (observationLeafVertex T i)
  | _, .fork T U => fun i=>Sum.elim
      (fun l=>.left (observationLeafVertex T l))
      (fun r=>.right (observationLeafVertex U r)) i

theorem observationLeafVertex_depth {j : ℕ} (T : FiniteTerminalGenealogy j) (i : ObservationLeaf T) :
    (observationLeafVertex T i).depth=0 := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih i
  | fork T U ihT ihU => cases i with
    | inl i => exact ihT i
    | inr i => exact ihU i

theorem observationLeaf_commonPathDepth {j : ℕ} (T : FiniteTerminalGenealogy j)
    (i k : ObservationLeaf T) :
    finiteCascadeCommonPathDepth T (observationLeafVertex T i) (observationLeafVertex T k)=
      observationCommonLevel T i k := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih i k
  | fork T U ihT ihU =>
      cases i with
      | inl i => cases k with
        | inl k => exact ihT i k
        | inr k => rfl
      | inr i => cases k with
        | inl k => rfl
        | inr k => exact ihU i k

theorem observationCommonLevel_self {j : ℕ} (T : FiniteTerminalGenealogy j) (i : ObservationLeaf T) :
    observationCommonLevel T i i=0 := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih i
  | fork T U ihT ihU => cases i with
    | inl i => exact ihT i
    | inr i => exact ihU i

theorem observationLeafSpin_treeMap {E F S : Type} (f : E→F) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (i : ObservationLeaf T) (z : Records E S T) :
    observationLeafSpin T i (observationTreeMap f T z)=observationLeafSpin T i z := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih i z.2
  | fork T U ihT ihU => cases i with
    | inl i => exact ihT i z.1
    | inr i => exact ihU i z.2

end FourPapersCommon
