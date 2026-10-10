module
public import QuantitativeFollowup.FollowupCavityGeneratedInitialForest
public import QuantitativeFollowup.AnisotropicRecordedPairCollapse

@[expose] public section

/-! Erasing unary observations retains the full binary branching shape,
all terminal spins and every physical pair clock when the original forks
occur at one chosen level. Diagonal pairs keep level zero. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def printedGeneratedInitialSiblingErasure : {J : ℕ} →
    FiniteTerminalGenealogy J → CavityGeneratedSiblingShape
  | _, .leaf => .single
  | _, .advance T => printedGeneratedInitialSiblingErasure T
  | _, .fork T U => .fork (printedGeneratedInitialSiblingErasure T)
      (printedGeneratedInitialSiblingErasure U)

@[reducible] def printedGeneratedInitialSiblingTerminalEquiv {A : Type} [MeasurableSpace A] :
    {J : ℕ} → (T : FiniteTerminalGenealogy J) →
      TerminalSpins A T ≃ᵐ TerminalSpins A (printedGeneratedInitialSiblingErasure T).tree
  | _, .leaf => MeasurableEquiv.refl A
  | _, .advance T => printedGeneratedInitialSiblingTerminalEquiv T
  | _, .fork T U => (printedGeneratedInitialSiblingTerminalEquiv T).prodCongr
      (printedGeneratedInitialSiblingTerminalEquiv U)

@[reducible] def printedGeneratedInitialSiblingLeafEquiv : {J : ℕ} →
    (T : FiniteTerminalGenealogy J) →
      ObservationLeaf T ≃ ObservationLeaf (printedGeneratedInitialSiblingErasure T).tree
  | _, .leaf => Equiv.refl _
  | _, .advance T => printedGeneratedInitialSiblingLeafEquiv T
  | _, .fork T U => Equiv.sumCongr (printedGeneratedInitialSiblingLeafEquiv T)
      (printedGeneratedInitialSiblingLeafEquiv U)

theorem printedGeneratedInitialSiblingErasure_leafCount {J : ℕ}
    (T : FiniteTerminalGenealogy J) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (printedGeneratedInitialSiblingErasure T).tree) =
      FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih
  | fork T U ihT ihU => exact congrArg₂ (fun x y : ℕ => x+y) ihT ihU

theorem printedGeneratedInitialSiblingTerminalEquiv_spin {A : Type} [MeasurableSpace A]
    {J : ℕ} (T : FiniteTerminalGenealogy J) (i : ObservationLeaf T)
    (σ : TerminalSpins A T) :
    observationTerminalSpin (printedGeneratedInitialSiblingErasure T).tree
      (printedGeneratedInitialSiblingLeafEquiv T i)
      (printedGeneratedInitialSiblingTerminalEquiv (A:=A) T σ) = observationTerminalSpin T i σ := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih i σ
  | fork T U ihT ihU => cases i with
    | inl i => exact ihT i σ.1
    | inr i => exact ihU i σ.2

@[reducible] def printedGeneratedInitialForksAt {A : Type*}
    (q : ℕ → A) (p : A) : {J : ℕ} → FiniteTerminalGenealogy J → Prop
  | _, .leaf => True
  | _, .advance T => printedGeneratedInitialForksAt q p T
  | J, .fork T U => q J = p ∧ printedGeneratedInitialForksAt q p T ∧
      printedGeneratedInitialForksAt q p U

theorem printedGeneratedInitialSiblingErasure_pair_clock {A : Type*} {J : ℕ}
    (T : FiniteTerminalGenealogy J) (q Q : ℕ → A) (p : A)
    (hzero : Q 0 = q 0) (hone : Q 1 = p)
    (hfork : printedGeneratedInitialForksAt q p T) (i k : ObservationLeaf T) :
    Q (observationCommonLevel (printedGeneratedInitialSiblingErasure T).tree
      (printedGeneratedInitialSiblingLeafEquiv T i)
      (printedGeneratedInitialSiblingLeafEquiv T k)) =
      q (observationCommonLevel T i k) := by
  induction T with
  | leaf => exact hzero
  | advance T ih => exact ih hfork i k
  | @fork j T U ihT ihU =>
      cases i with
      | inl i => cases k with
        | inl k => exact ihT hfork.2.1 i k
        | inr k => exact hone.trans hfork.1.symm
      | inr i => cases k with
        | inl k => exact hone.trans hfork.1.symm
        | inr k => exact ihU hfork.2.2 i k

theorem printedGeneratedInitialSiblingErasure_has_fork {A : Type*} {J : ℕ}
    (T : FiniteTerminalGenealogy J) (q : ℕ → A) (p : A)
    (hfork : printedGeneratedInitialForksAt q p T)
    (hnot : printedGeneratedInitialSiblingErasure T ≠ .single) :
    ∃ j, j ≤ J ∧ q j = p := by
  induction T with
  | leaf => exact (hnot rfl).elim
  | advance T ih =>
      obtain ⟨j,hj,hq⟩ := ih hfork hnot
      exact ⟨j,hj.trans (Nat.le_succ _),hq⟩
  | @fork j T U ihT ihU => exact ⟨j,le_rfl,hfork.1⟩

end QuantitativeFollowup
