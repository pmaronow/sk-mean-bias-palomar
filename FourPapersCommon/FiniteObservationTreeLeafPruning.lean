module
public import FourPapersCommon.FiniteObservationTreePruning

@[expose] public section

/-! Keeping a chosen terminal descendant preserves its complete ancestral
field record. The retained tree is the actual single continuation chain. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy FiniteObservationPruning
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def observationLinearTree : (j : ℕ)→FiniteTerminalGenealogy j
  | 0 => .leaf
  | j+1 => .advance (observationLinearTree j)

@[reducible] def ObservationLeaf : {j : ℕ}→FiniteTerminalGenealogy j→Type
  | _, .leaf => Unit
  | _, .advance T => ObservationLeaf T
  | _, .fork T U => ObservationLeaf T⊕ObservationLeaf U

@[reducible] def observationLeafSpin {E S : Type} : {j : ℕ}→(T : FiniteTerminalGenealogy j)→
    ObservationLeaf T→Records E S T→S
  | _, .leaf => fun _ => id
  | _, .advance T => fun i => observationLeafSpin T i ∘ Prod.snd
  | _, .fork T U => fun i v => Sum.elim
      (fun l => observationLeafSpin T l v.1)
      (fun r => observationLeafSpin U r v.2) i

@[reducible] def observationLinearSpin {E S : Type} : (j : ℕ)→Records E S (observationLinearTree j)→S
  | 0 => id
  | j+1 => observationLinearSpin j ∘ Prod.snd

@[reducible] def observationLeafPruning : {j : ℕ}→(T : FiniteTerminalGenealogy j)→
    ObservationLeaf T→FiniteObservationPruning T (observationLinearTree j)
  | _, .leaf => fun _ => .refl .leaf
  | _, .advance T => fun i => .advance (observationLeafPruning T i)
  | _, .fork T U => fun i => Sum.elim
      (fun l => .left U (observationLeafPruning T l))
      (fun r => .right T (observationLeafPruning U r)) i

theorem observationLeafPruning_spin {E S : Type} {j : ℕ} (T : FiniteTerminalGenealogy j)
    (i : ObservationLeaf T) :
    observationLinearSpin (E:=E) (S:=S) j ∘ project (observationLeafPruning T i)=
      observationLeafSpin T i := by
  induction T with
  | leaf => rfl
  | advance T ih =>
      funext v
      exact congrFun (ih i) v.2
  | fork T U ihT ihU =>
      cases i with
      | inl i => funext v;exact congrFun (ihT i) v.1
      | inr i => funext v;exact congrFun (ihU i) v.2

theorem measurable_observationLeafSpin {E S : Type} [MeasurableSpace E] [MeasurableSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (i : ObservationLeaf T) :
    Measurable (observationLeafSpin (E:=E) (S:=S) T i) := by
  induction T with
  | leaf => exact measurable_id
  | advance T ih => exact (ih i).comp measurable_snd
  | fork T U ihT ihU =>
      cases i with
      | inl i => exact (ihT i).comp measurable_fst
      | inr i => exact (ihU i).comp measurable_snd

theorem measurable_observationLinearSpin {E S : Type} [MeasurableSpace E] [MeasurableSpace S]
    (j : ℕ) : Measurable (observationLinearSpin (E:=E) (S:=S) j) := by
  induction j with
  | zero => exact measurable_id
  | succ j ih => exact ih.comp measurable_snd

theorem continuous_observationLeafSpin {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (i : ObservationLeaf T) :
    Continuous (observationLeafSpin (E:=E) (S:=S) T i) := by
  induction T with
  | leaf => exact continuous_id
  | advance T ih => exact (ih i).comp continuous_snd
  | fork T U ihT ihU =>
      cases i with
      | inl i => exact (ihT i).comp continuous_fst
      | inr i => exact (ihU i).comp continuous_snd

end FourPapersCommon
