module
public import FourPapersCommon.FiniteCascadeTreeReferenceFlatDensity
public import FourPapersCommon.FiniteCascadeTreeReferenceRootFields

@[expose] public section

/-! The separated terminal-spin factor is literally counting measure on the
finite product of terminal spins. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy
namespace FiniteTerminalGenealogy

@[reducible] def terminalSpinsFintype (S : Type) [Fintype S] :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → Fintype (TerminalSpins S T)
  | _, .leaf => inferInstanceAs (Fintype S)
  | _, .advance T => terminalSpinsFintype S T
  | _, .fork T U => by
      letI := terminalSpinsFintype S T
      letI := terminalSpinsFintype S U
      exact inferInstanceAs (Fintype (TerminalSpins S T × TerminalSpins S U))

instance instFintypeTerminalSpins (S : Type) [Fintype S] {j : ℕ}
    (T : FiniteTerminalGenealogy j) : Fintype (TerminalSpins S T) := terminalSpinsFintype S T

@[reducible] def terminalSpinsMeasurableSingletonClass (S : Type)
    [MeasurableSpace S] [MeasurableSingletonClass S] :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → MeasurableSingletonClass (TerminalSpins S T)
  | _, .leaf => inferInstanceAs (MeasurableSingletonClass S)
  | _, .advance T => terminalSpinsMeasurableSingletonClass S T
  | _, .fork T U => by
      letI := terminalSpinsMeasurableSingletonClass S T
      letI := terminalSpinsMeasurableSingletonClass S U
      exact inferInstanceAs (MeasurableSingletonClass (TerminalSpins S T × TerminalSpins S U))

instance instMeasurableSingletonClassTerminalSpins (S : Type)
    [MeasurableSpace S] [MeasurableSingletonClass S] {j : ℕ}
    (T : FiniteTerminalGenealogy j) : MeasurableSingletonClass (TerminalSpins S T) :=
  terminalSpinsMeasurableSingletonClass S T

theorem terminalSpinCountingLaw_eq_count (S : Type) [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S] {j : ℕ}
    (T : FiniteTerminalGenealogy j) : terminalSpinCountingLaw S T = Measure.count := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih
  | fork T U ihT ihU =>
      change (terminalSpinCountingLaw S T).prod (terminalSpinCountingLaw S U) = Measure.count
      rw [ihT,ihU]
      apply Measure.ext_of_singleton
      intro p
      rcases p with ⟨x,y⟩
      calc
        ((Measure.count : Measure (TerminalSpins S T)).prod Measure.count) {(x,y)} =
            (Measure.count : Measure (TerminalSpins S T)) {x} *
              (Measure.count : Measure (TerminalSpins S U)) {y} := by
          rw [←Set.singleton_prod_singleton,Measure.prod_prod]
        _ = Measure.count {(x,y)} := by simp

end FiniteTerminalGenealogy
end FourPapersCommon
