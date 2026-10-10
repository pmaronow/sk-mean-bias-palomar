module
public import FourPapersCommon.FiniteCascadeReferenceTerminalProjection

@[expose] public section

/-! Exact identification of the independent terminal-spin product with
the original finite genealogy's spin sample, retaining all branches. -/
noncomputable section
namespace FourPapersCommon
open FiniteTerminalGenealogy
namespace FiniteTerminalGenealogy

@[reducible] def terminalSampleEquiv {S : Type} [MeasurableSpace S] :
    {j : ℕ}→(T : FiniteTerminalGenealogy j)→
      TerminalSpins S T≃ᵐFiniteCascadeGenealogy.Samples S (asGenealogy T)
  | _,.leaf => MeasurableEquiv.refl _
  | _,.advance T => terminalSampleEquiv T
  | _,.fork T U => (terminalSampleEquiv T).prodCongr (terminalSampleEquiv U)

theorem terminalSampleEquiv_recordSpins {E S : Type} [MeasurableSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (p : Records E S T) :
    terminalSampleEquiv (S:=S) T (finiteCascadeRecordTerminalSpins T p)=spins T p := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih p.2
  | fork T U ihT ihU => exact congrArg₂ Prod.mk (ihT p.1) (ihU p.2)

end FiniteTerminalGenealogy
end FourPapersCommon
