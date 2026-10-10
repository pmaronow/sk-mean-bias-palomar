module
public import FourPapersCommon.FiniteObservationTreeLeafPruning

@[expose] public section

/-! Two chosen distinct terminal descendants retain exactly one common
ancestral chain, followed by two independent complete continuations. The
split level is computed from the original genealogy. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy FiniteObservationPruning
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

inductive ObservationPairTree : ℕ→Type
  | split (j : ℕ) (reverse : Bool) : ObservationPairTree j
  | advance {j : ℕ} : ObservationPairTree j→ObservationPairTree (j+1)

namespace ObservationPairTree
@[reducible] def tree : {j : ℕ}→ObservationPairTree j→FiniteTerminalGenealogy j
  | _, .split j _ => .fork (observationLinearTree j) (observationLinearTree j)
  | _, .advance P => .advance P.tree
@[reducible] def splitLevel : {j : ℕ}→ObservationPairTree j→ℕ
  | _, .split j _ => j
  | _, .advance P => P.splitLevel
@[reducible] def spins {E S : Type} : {j : ℕ}→(P : ObservationPairTree j)→Records E S P.tree→S×S
  | _, .split j false => fun v=>(observationLinearSpin j v.1,observationLinearSpin j v.2)
  | _, .split j true => fun v=>(observationLinearSpin j v.2,observationLinearSpin j v.1)
  | _, .advance P => P.spins ∘ Prod.snd

theorem splitLevel_le {j : ℕ} (P : ObservationPairTree j) : P.splitLevel≤j := by
  induction P with
  | split j reverse => exact le_rfl
  | advance P ih => exact ih.trans (Nat.le_succ _)

theorem measurable_spins {E S : Type} [MeasurableSpace E] [MeasurableSpace S]
    {j : ℕ} (P : ObservationPairTree j) : Measurable (P.spins (E:=E) (S:=S)) := by
  induction P with
  | split j reverse =>
      cases reverse with
      | false =>
          exact ((measurable_observationLinearSpin (E:=E) (S:=S) j).comp measurable_fst).prodMk
            ((measurable_observationLinearSpin (E:=E) (S:=S) j).comp measurable_snd)
      | true =>
          exact ((measurable_observationLinearSpin (E:=E) (S:=S) j).comp measurable_snd).prodMk
            ((measurable_observationLinearSpin (E:=E) (S:=S) j).comp measurable_fst)
  | advance P ih => exact ih.comp measurable_snd
end ObservationPairTree

@[reducible] def observationCommonLevel : {j : ℕ}→(T : FiniteTerminalGenealogy j)→
    ObservationLeaf T→ObservationLeaf T→ℕ
  | _, .leaf => fun _ _ => 0
  | _, .advance T => observationCommonLevel T
  | j, .fork T U => fun i k => Sum.elim
      (fun l => Sum.elim (fun r => observationCommonLevel T l r) (fun _ => j) k)
      (fun l => Sum.elim (fun _ => j) (fun r => observationCommonLevel U l r) k) i

theorem exists_observationPairPruning {E S : Type} {j : ℕ} (T : FiniteTerminalGenealogy j)
    (i k : ObservationLeaf T) (hik : i≠k) :
    ∃ (P : ObservationPairTree j) (R : FiniteObservationPruning T P.tree),
      P.splitLevel=observationCommonLevel T i k ∧
        P.spins (E:=E) (S:=S) ∘ project R=(fun v=>(observationLeafSpin T i v,observationLeafSpin T k v)) := by
  induction T with
  | leaf => exact (hik (Subsingleton.elim i k)).elim
  | advance T ih =>
      obtain ⟨P,R,hlevel,hspin⟩:=ih i k hik
      refine ⟨.advance P,.advance R,hlevel,?_⟩
      funext v
      exact congrFun hspin v.2
  | @fork j T U ihT ihU =>
      cases i with
      | inl i =>
          cases k with
          | inl k =>
              obtain ⟨P,R,hlevel,hspin⟩:=ihT i k (fun h=>hik (congrArg Sum.inl h))
              refine ⟨P,.left U R,hlevel,?_⟩
              funext v
              exact congrFun hspin v.1
          | inr k =>
              refine ⟨.split j false,.fork (observationLeafPruning T i) (observationLeafPruning U k),rfl,?_⟩
              funext v
              exact Prod.ext (congrFun (observationLeafPruning_spin T i) v.1)
                (congrFun (observationLeafPruning_spin U k) v.2)
      | inr i =>
          cases k with
          | inl k =>
              refine ⟨.split j true,.fork (observationLeafPruning T k) (observationLeafPruning U i),rfl,?_⟩
              funext v
              exact Prod.ext (congrFun (observationLeafPruning_spin U i) v.2)
                (congrFun (observationLeafPruning_spin T k) v.1)
          | inr k =>
              obtain ⟨P,R,hlevel,hspin⟩:=ihU i k (fun h=>hik (congrArg Sum.inr h))
              refine ⟨P,.right T R,hlevel,?_⟩
              funext v
              exact congrFun hspin v.2

end FourPapersCommon
