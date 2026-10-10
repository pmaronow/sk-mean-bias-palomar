module
public import FourPapersCommon.FiniteCascadeZeroRoot
public import FourPapersCommon.FiniteCascadeTerminalSampleEquiv
public import FourPapersCommon.FiniteObservationLeafGeometry
public import FourPapersCommon.FiniteCascadeChargeLevels

@[expose] public section

/-! Deleting the first unary edge preserves actual terminal descendants.
Only forks preceding that edge change their common level, from j to j-1. -/
noncomputable section
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 700000

@[reducible] def observationTrimLeaf : {j : ℕ} → (T : FiniteTerminalGenealogy j) →
    ObservationLeaf T → ObservationLeaf (trimRoot T)
  | _, .leaf => id
  | _, .advance _ => id
  | _, .fork T U => Sum.map (observationTrimLeaf T) (observationTrimLeaf U)

theorem observationTrimLeaf_spin {E S : Type} {j : ℕ} (T : FiniteTerminalGenealogy j)
    (i : ObservationLeaf T) (z : Records E S T) :
    observationLeafSpin (trimRoot T) (observationTrimLeaf T i) (trimRecords T z) =
      observationLeafSpin T i z := by
  induction T with
  | leaf => rfl
  | advance T => rfl
  | fork T U ihT ihU => cases i with
    | inl i => exact ihT i z.1
    | inr i => exact ihU i z.2

theorem observationTrimLeaf_injective {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Function.Injective (observationTrimLeaf T) := by
  induction T with
  | leaf => exact Function.injective_id
  | advance T => exact Function.injective_id
  | fork T U ihT ihU => exact Sum.map_injective.mpr ⟨ihT,ihU⟩

theorem observationTrimLeaf_surjective {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Function.Surjective (observationTrimLeaf T) := by
  induction T with
  | leaf => exact Function.surjective_id
  | advance T => exact Function.surjective_id
  | fork T U ihT ihU =>
      intro i
      cases i with
      | inl i => obtain ⟨a,ha⟩ := ihT i; exact ⟨Sum.inl a, congrArg Sum.inl ha⟩
      | inr i => obtain ⟨a,ha⟩ := ihU i; exact ⟨Sum.inr a, congrArg Sum.inr ha⟩

theorem observationTrimLeaf_commonLevel {j : ℕ} (T : FiniteTerminalGenealogy j)
    (i k : ObservationLeaf T) :
    observationCommonLevel (trimRoot T) (observationTrimLeaf T i) (observationTrimLeaf T k) =
        observationCommonLevel T i k ∨
      (observationCommonLevel T i k = j ∧
        observationCommonLevel (trimRoot T) (observationTrimLeaf T i) (observationTrimLeaf T k) = j-1) := by
  induction T with
  | leaf => exact Or.inl rfl
  | advance T => exact Or.inl rfl
  | @fork j T U ihT ihU =>
      cases i with
      | inl i => cases k with
        | inl k => exact ihT i k
        | inr k => exact Or.inr ⟨rfl,rfl⟩
      | inr i => cases k with
        | inl k => exact Or.inr ⟨rfl,rfl⟩
        | inr k => exact ihU i k

theorem observationTrimLeaf_commonLevel_clock (q : ℕ → ℝ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (hq : q j = q (j-1)) (i k : ObservationLeaf T) :
    q (observationCommonLevel (trimRoot T) (observationTrimLeaf T i) (observationTrimLeaf T k)) =
      q (observationCommonLevel T i k) := by
  rcases observationTrimLeaf_commonLevel T i k with he | ⟨ho,hn⟩
  · rw [he]
  · rw [ho,hn]; exact hq.symm

theorem finiteCascadeUnweightedBranchSum_trimRoot (χ : ℕ → ℝ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (hχ : χ j = χ (j-1)) :
    finiteCascadeUnweightedBranchSum χ (trimRoot T) = finiteCascadeUnweightedBranchSum χ T := by
  induction T with
  | leaf => rfl
  | advance T => rfl
  | @fork j T U ihT ihU =>
      change finiteCascadeUnweightedBranchSum χ (trimRoot T) +
          finiteCascadeUnweightedBranchSum χ (trimRoot U) + χ (j-1) =
        finiteCascadeUnweightedBranchSum χ T + finiteCascadeUnweightedBranchSum χ U + χ j
      rw [ihT hχ,ihU hχ,hχ]

@[reducible] def observationLeafTerminalSpin {S : Type} : {j : ℕ} →
    (T : FiniteTerminalGenealogy j) → ObservationLeaf T → TerminalSpins S T → S
  | _, .leaf => fun _ => id
  | _, .advance T => observationLeafTerminalSpin T
  | _, .fork T U => fun i z => Sum.elim
      (fun l => observationLeafTerminalSpin T l z.1)
      (fun r => observationLeafTerminalSpin U r z.2) i

theorem observationLeafTerminalSpin_record {E S : Type} {j : ℕ}
    (T : FiniteTerminalGenealogy j) (i : ObservationLeaf T) (z : Records E S T) :
    observationLeafTerminalSpin T i (finiteCascadeRecordTerminalSpins T z) = observationLeafSpin T i z := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih i z.2
  | fork T U ihT ihU => cases i with
    | inl i => exact ihT i z.1
    | inr i => exact ihU i z.2

theorem observationTrimLeaf_terminalSpin {S : Type} [MeasurableSpace S] {j : ℕ}
    (T : FiniteTerminalGenealogy j) (i : ObservationLeaf T) (z : TerminalSpins S (trimRoot T)) :
    observationLeafTerminalSpin (S:=S) T i
      ((terminalSampleEquiv (S:=S) T).symm (trimmedSpinEquiv (S:=S) T
        (terminalSampleEquiv (S:=S) (trimRoot T) z))) =
      observationLeafTerminalSpin (S:=S) (trimRoot T) (observationTrimLeaf T i) z := by
  induction T with
  | leaf => rfl
  | advance T => simp only [trimRoot,terminalSampleEquiv,trimmedSpinEquiv,
      MeasurableEquiv.refl_apply,MeasurableEquiv.symm_apply_apply,
      observationLeafTerminalSpin,observationTrimLeaf,Function.id_def]
  | fork T U ihT ihU => cases i with
    | inl i => exact ihT i z.1
    | inr i => exact ihU i z.2

end FourPapersCommon
