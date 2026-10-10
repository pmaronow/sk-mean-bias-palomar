module
public import FourPapersCommon.FiniteObservationTerminalProjection
public import FourPapersCommon.FiniteObservationRefinementLeafGeometry

@[expose] public section

/-! The literal terminal projection of an observation refinement
extracts exactly the embedded original terminal leaves. -/
noncomputable section
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128

theorem finiteCascadeRecordTerminalSpins_unit {S : Type} {j : ℕ}
    (T : FiniteTerminalGenealogy j) (σ : TerminalSpins S T) :
    finiteCascadeRecordTerminalSpins T (observationUnitRecord T σ)=σ := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih σ
  | fork T U ihT ihU => exact congrArg₂ Prod.mk (ihT σ.1) (ihU σ.2)

theorem observationRefinementTerminalProject_leaf {S : Type} (d : ℕ → ℕ) {j l : ℕ}
    (T : FiniteTerminalGenealogy j) (h : observationRefinementDepth d j=l)
    (i : ObservationLeaf T)
    (σ : TerminalSpins S (observationTreeDepthCast h (observationRefineTree d T))) :
    observationTerminalSpin T i (observationRefinementTerminalProject d T h σ)=
      observationTerminalSpin _ (observationRefinementDepthLeafEmbed d T h i) σ := by
  unfold observationRefinementTerminalProject
  rw [observationTerminalSpin_record,←observationRefinementDepthLeafEmbed_spin,
    ←observationTerminalSpin_record,finiteCascadeRecordTerminalSpins_unit]

end FourPapersCommon
