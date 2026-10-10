module
public import QuantitativeFollowup.SupportingGeneratedInitialSiblingErasureGeometry
public import FourPapersCommon.FiniteObservationRefinementTerminalLeaves

@[expose] public section

/-! Unary-only observation refinements preserve the actual branching shape,
all original fork clocks, and the literal terminal/leaf erasure maps. -/
noncomputable section
open MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem printedGeneratedInitialPad_erasure {J : ℕ}
    (T : FiniteTerminalGenealogy J) (k : ℕ) :
    printedGeneratedInitialSiblingErasure (observationTreePad T k) =
      printedGeneratedInitialSiblingErasure T := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

theorem printedGeneratedInitialRefinement_erasure (d : ℕ → ℕ) {J : ℕ}
    (T : FiniteTerminalGenealogy J) :
    printedGeneratedInitialSiblingErasure (observationRefineTree d T) =
      printedGeneratedInitialSiblingErasure T := by
  induction T with
  | leaf => rfl
  | @advance j T ih => exact (printedGeneratedInitialPad_erasure _ (d j)).trans ih
  | fork T U ihT ihU => exact congrArg₂ CavityGeneratedSiblingShape.fork ihT ihU

theorem printedGeneratedInitialPad_forksAt {A : Type*} (Q : ℕ → A) (p : A)
    {J : ℕ} (T : FiniteTerminalGenealogy J) (k : ℕ) :
    printedGeneratedInitialForksAt Q p (observationTreePad T k) ↔
      printedGeneratedInitialForksAt Q p T := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

theorem printedGeneratedInitialRefinement_forksAt {A : Type*}
    (q Q : ℕ → A) (d : ℕ → ℕ) (p : A)
    (hlevels : ∀ j, Q (observationRefinementDepth d j) = q j)
    {J : ℕ} (T : FiniteTerminalGenealogy J)
    (hfork : printedGeneratedInitialForksAt q p T) :
    printedGeneratedInitialForksAt Q p (observationRefineTree d T) := by
  induction T with
  | leaf => trivial
  | @advance j T ih =>
      exact (printedGeneratedInitialPad_forksAt Q p _ (d j)).mpr (ih hfork)
  | @fork j T U ihT ihU =>
      exact ⟨(hlevels j).trans hfork.1, ihT hfork.2.1, ihU hfork.2.2⟩

@[reducible] def printedGeneratedInitialPadTerminalEquiv {S : Type}
    [MeasurableSpace S] {J : ℕ} (T : FiniteTerminalGenealogy J) :
    (k : ℕ) → TerminalSpins S (observationTreePad T k) ≃ᵐ TerminalSpins S T
  | 0 => MeasurableEquiv.refl _
  | k+1 => printedGeneratedInitialPadTerminalEquiv T k

@[reducible] def printedGeneratedInitialRefinementTerminalEquiv {S : Type}
    [MeasurableSpace S] (d : ℕ → ℕ) : {J : ℕ} → (T : FiniteTerminalGenealogy J) →
    TerminalSpins S (observationRefineTree d T) ≃ᵐ TerminalSpins S T
  | _, .leaf => MeasurableEquiv.refl _
  | _, @FiniteTerminalGenealogy.advance j T =>
      (printedGeneratedInitialPadTerminalEquiv _ (d j)).trans
        (printedGeneratedInitialRefinementTerminalEquiv d T)
  | _, .fork T U => (printedGeneratedInitialRefinementTerminalEquiv d T).prodCongr
      (printedGeneratedInitialRefinementTerminalEquiv d U)

private theorem initialTerminal_ext {S : Type} {J : ℕ}
    (T : FiniteTerminalGenealogy J) (σ τ : TerminalSpins S T)
    (h : ∀ i, observationTerminalSpin T i σ = observationTerminalSpin T i τ) : σ = τ := by
  induction T with
  | leaf => exact h PUnit.unit
  | advance T ih => exact ih σ τ h
  | fork T U ihT ihU =>
      exact Prod.ext (ihT σ.1 τ.1 (fun i => h (.inl i)))
        (ihU σ.2 τ.2 (fun i => h (.inr i)))

private theorem initialPadTerminal_spin {S : Type} [MeasurableSpace S] {J : ℕ}
    (T : FiniteTerminalGenealogy J) (k : ℕ) (i : ObservationLeaf T)
    (σ : TerminalSpins S (observationTreePad T k)) :
    observationTerminalSpin T i (printedGeneratedInitialPadTerminalEquiv (S:=S) T k σ) =
      observationTerminalSpin (observationTreePad T k) (observationPadLeafEmbed T k i) σ := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih σ

theorem printedGeneratedInitialRefinementTerminalEquiv_spin {S : Type}
    [MeasurableSpace S] (d : ℕ → ℕ) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (i : ObservationLeaf T) (σ : TerminalSpins S (observationRefineTree d T)) :
    observationTerminalSpin T i (printedGeneratedInitialRefinementTerminalEquiv (S:=S) d T σ) =
      observationTerminalSpin (observationRefineTree d T) (observationRefinementLeafEmbed d T i) σ := by
  induction T with
  | leaf => rfl
  | @advance j T ih =>
      exact (ih i (printedGeneratedInitialPadTerminalEquiv (S:=S) (observationRefineTree d T) (d j) σ)).trans
        (initialPadTerminal_spin _ (d j) _ σ)
  | fork T U ihT ihU => cases i with
    | inl i => exact ihT i σ.1
    | inr i => exact ihU i σ.2

theorem printedGeneratedInitialRefinementTerminalEquiv_eq_project {S : Type}
    [MeasurableSpace S] (d : ℕ → ℕ) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (σ : TerminalSpins S (observationRefineTree d T)) :
    printedGeneratedInitialRefinementTerminalEquiv (S:=S) d T σ =
      observationRefinementTerminalProject d T rfl σ := by
  apply initialTerminal_ext T
  intro i
  rw [printedGeneratedInitialRefinementTerminalEquiv_spin]
  exact (observationRefinementTerminalProject_leaf d T rfl i σ).symm

private theorem initialPair_heq {A B C D : Type} {a : A} {b : B} {c : C} {d : D}
    (ha : HEq a c) (hb : HEq b d) : HEq (a,b) (c,d) := by
  cases ha
  cases hb
  rfl

private theorem initialPad_erasedTerminal {S : Type} [MeasurableSpace S] {J : ℕ}
    (T : FiniteTerminalGenealogy J) (k : ℕ) (σ : TerminalSpins S (observationTreePad T k)) :
    HEq (printedGeneratedInitialSiblingTerminalEquiv (A:=S) (observationTreePad T k) σ)
      (printedGeneratedInitialSiblingTerminalEquiv (A:=S) T (printedGeneratedInitialPadTerminalEquiv (S:=S) T k σ)) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih σ

theorem printedGeneratedInitialRefinement_erasedTerminal {S : Type} [MeasurableSpace S]
    (d : ℕ → ℕ) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (σ : TerminalSpins S (observationRefineTree d T)) :
    HEq (printedGeneratedInitialSiblingTerminalEquiv (A:=S) (observationRefineTree d T) σ)
      (printedGeneratedInitialSiblingTerminalEquiv (A:=S) T
        (observationRefinementTerminalProject d T rfl σ)) := by
  rw [←printedGeneratedInitialRefinementTerminalEquiv_eq_project]
  induction T with
  | leaf => rfl
  | @advance j T ih =>
      exact (initialPad_erasedTerminal _ (d j) σ).trans
        (ih (printedGeneratedInitialPadTerminalEquiv (S:=S) (observationRefineTree d T) (d j) σ))
  | fork T U ihT ihU => exact initialPair_heq (ihT σ.1) (ihU σ.2)

private theorem initialInl_heq {A B C D : Type} {a : A} {c : C}
    (ha : HEq a c) (hBD : B = D) : HEq (Sum.inl a : A ⊕ B) (Sum.inl c : C ⊕ D) := by
  cases hBD
  cases ha
  rfl

private theorem initialInr_heq {A B C D : Type} {b : B} {d : D}
    (hAC : A = C) (hb : HEq b d) : HEq (Sum.inr b : A ⊕ B) (Sum.inr d : C ⊕ D) := by
  cases hAC
  cases hb
  rfl

private theorem initialPad_erasedLeaf {J : ℕ} (T : FiniteTerminalGenealogy J)
    (k : ℕ) (i : ObservationLeaf T) :
    HEq (printedGeneratedInitialSiblingLeafEquiv (observationTreePad T k)
      (observationPadLeafEmbed T k i)) (printedGeneratedInitialSiblingLeafEquiv T i) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

theorem printedGeneratedInitialRefinement_erasedLeaf (d : ℕ → ℕ) {J : ℕ}
    (T : FiniteTerminalGenealogy J) (i : ObservationLeaf T) :
    HEq (printedGeneratedInitialSiblingLeafEquiv (observationRefineTree d T)
      (observationRefinementLeafEmbed d T i)) (printedGeneratedInitialSiblingLeafEquiv T i) := by
  induction T with
  | leaf => rfl
  | @advance j T ih => exact (initialPad_erasedLeaf _ (d j) _).trans (ih i)
  | fork T U ihT ihU => cases i with
    | inl i =>
        exact initialInl_heq (ihT i)
          (congrArg (fun S => ObservationLeaf S.tree) (printedGeneratedInitialRefinement_erasure d U))
    | inr i =>
        exact initialInr_heq
          (congrArg (fun S => ObservationLeaf S.tree) (printedGeneratedInitialRefinement_erasure d T)) (ihU i)

end QuantitativeFollowup
