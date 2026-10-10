module
public import FourPapersCommon.FiniteCascadeFuturePairTree
public import FourPapersCommon.FiniteObservationLeafGeometry

@[expose] public section

/-! The two future marks are actual distinct leaves, whose common
ancestor is the declared future split. -/
noncomputable section
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 700000

@[reducible] def observationLinearLeaf : (d : ℕ)→ObservationLeaf (observationLinearTree d)
  | 0 => ()
  | d+1 => observationLinearLeaf d

@[reducible] def observationPairFirstLeaf : {d : ℕ}→(P : ObservationPairTree d)→ObservationLeaf P.tree
  | _,.split d false => .inl (observationLinearLeaf d)
  | _,.split d true => .inr (observationLinearLeaf d)
  | _,.advance P => observationPairFirstLeaf P

@[reducible] def observationPairSecondLeaf : {d : ℕ}→(P : ObservationPairTree d)→ObservationLeaf P.tree
  | _,.split d false => .inr (observationLinearLeaf d)
  | _,.split d true => .inl (observationLinearLeaf d)
  | _,.advance P => observationPairSecondLeaf P

private theorem linearLeaf_spin {E S : Type} (d : ℕ) (z : Records E S (observationLinearTree d)) :
    observationLeafSpin (observationLinearTree d) (observationLinearLeaf d) z=observationLinearSpin d z := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih z.2

theorem observationPair_spins_eq_leaf_pair {E S : Type} {d : ℕ} (P : ObservationPairTree d)
    (z : Records E S P.tree) :
    P.spins z=(observationLeafSpin P.tree (observationPairFirstLeaf P) z,
      observationLeafSpin P.tree (observationPairSecondLeaf P) z) := by
  induction P with
  | split d reverse =>
      cases reverse <;> simp only [ObservationPairTree.spins,observationPairFirstLeaf,
        observationPairSecondLeaf,ObservationPairTree.tree,observationLeafSpin,
        Sum.elim_inl,Sum.elim_inr,linearLeaf_spin]
  | advance P ih => exact ih z.2

theorem observationPair_first_ne_second {d : ℕ} (P : ObservationPairTree d) :
    observationPairFirstLeaf P≠observationPairSecondLeaf P := by
  induction P with
  | split d reverse => cases reverse <;> simp only [observationPairFirstLeaf,
      observationPairSecondLeaf,ne_eq,reduceCtorEq,not_false_eq_true]
  | advance P ih => exact ih

theorem observationPair_commonLevel {d : ℕ} (P : ObservationPairTree d) :
    observationCommonLevel P.tree (observationPairFirstLeaf P) (observationPairSecondLeaf P)=P.splitLevel := by
  induction P with
  | split d reverse => cases reverse <;> rfl
  | advance P ih => exact ih

end FourPapersCommon
