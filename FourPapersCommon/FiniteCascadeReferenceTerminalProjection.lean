module
public import FourPapersCommon.FiniteCascadeTreeReferenceSpins

@[expose] public section

/-! The terminal-spin projection of the actual field record. Independent
Gaussian realization preserves these marks exactly. -/
noncomputable section
open MeasureTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
variable {E S I : Type} [Fintype S] [Fintype I]

@[reducible] def finiteCascadeRecordTerminalSpins : {j : ℕ}→(T : FiniteTerminalGenealogy j)→
    Records E S T→TerminalSpins S T
  | _,.leaf => id
  | _,.advance T => finiteCascadeRecordTerminalSpins T ∘ Prod.snd
  | _,.fork T U => Prod.map (finiteCascadeRecordTerminalSpins T) (finiteCascadeRecordTerminalSpins U)

theorem measurable_finiteCascadeRecordTerminalSpins [MeasurableSpace E] [MeasurableSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (finiteCascadeRecordTerminalSpins (E:=E) (S:=S) T) := by
  induction T with
  | leaf => exact measurable_id
  | advance T ih => exact ih.comp measurable_snd
  | fork T U ihT ihU => exact ihT.prodMap ihU

theorem finiteCascadeRecordTerminalSpins_referenceFlat
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : FiniteStateGaussianInput (GaussianCoordinateIndex I T)) (σ : TerminalSpins S T) :
    finiteCascadeRecordTerminalSpins T (finiteCascadeTreeReferenceFlatRecord L T H (z,σ))=σ := by
  induction T generalizing H with
  | leaf => rfl
  | @advance j T ih => exact ih (H+L j (finiteGaussianLeft z)) (finiteGaussianRight z) σ
  | fork T U ihT ihU =>
    exact congrArg₂ Prod.mk
      (ihT H (finiteGaussianLeft z) σ.1) (ihU H (finiteGaussianRight z) σ.2)

theorem finiteCascadeRecordTerminalSpins_referenceRoot
    [Fintype E] (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput E→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (z : FiniteStateGaussianInput (E ⊕ GaussianCoordinateIndex I T)) (σ : TerminalSpins S T) :
    finiteCascadeRecordTerminalSpins T (finiteCascadeTreeReferenceRootFlatRecord L T R H (z,σ)).2=σ :=
  finiteCascadeRecordTerminalSpins_referenceFlat L T (H+R (finiteGaussianLeft z))
    (finiteGaussianRight z) σ

end FourPapersCommon
