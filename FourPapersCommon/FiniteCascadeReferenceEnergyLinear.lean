module
public import FourPapersCommon.FiniteCascadeTreeVertexLinear
public import FourPapersCommon.FiniteCascadeTreeCharges

@[expose] public section

/-! The terminal energy of each fixed marked genealogy is literally a
continuous linear function of the independent Gaussian coordinates. -/
noncomputable section
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {S I : Type} [Fintype S] [Fintype I]

@[reducible] def finiteCascadeReferenceTerminalEnergyCLM
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) :
    {j : ℕ}→(T : FiniteTerminalGenealogy j)→TerminalSpins S T→
      (FiniteStateField S×FiniteStateGaussianInput (GaussianCoordinateIndex I T)→L[ℝ]ℝ)
  | _,.leaf,σ => (EuclideanSpace.proj σ).comp (ContinuousLinearMap.fst ℝ _ _)
  | _,@FiniteTerminalGenealogy.advance j T,σ =>
      (finiteCascadeReferenceTerminalEnergyCLM L T σ).comp
        ((ContinuousLinearMap.fst ℝ (FiniteStateField S) _ +
          (L j).comp (finiteGaussianLeft.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S) _))).prod
            (finiteGaussianRight.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S) _)))
  | _,.fork T U,σ =>
      (finiteCascadeReferenceTerminalEnergyCLM L T σ.1).comp
        ((ContinuousLinearMap.fst ℝ (FiniteStateField S) _).prod
          (finiteGaussianLeft.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S) _))) +
      (finiteCascadeReferenceTerminalEnergyCLM L U σ.2).comp
        ((ContinuousLinearMap.fst ℝ (FiniteStateField S) _).prod
          (finiteGaussianRight.comp (ContinuousLinearMap.snd ℝ (FiniteStateField S) _)))

theorem finiteCascadeReference_terminalEnergy_eq_clm
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (σ : TerminalSpins S T)
    (H : FiniteStateField S) (z : FiniteStateGaussianInput (GaussianCoordinateIndex I T)) :
    finiteCascadeTreeTerminalEnergy (fun _ : S=>0) T H
      (finiteCascadeTreeReferenceFlatRecord L T H (z,σ)) =
        finiteCascadeReferenceTerminalEnergyCLM L T σ (H,z) := by
  induction T generalizing H with
  | leaf => simp only [finiteCascadeTreeTerminalEnergy,finiteCascadeTreeReferenceFlatRecord,
      finiteCascadeTreeReferenceRecord,finiteCascadeReferenceTerminalEnergyCLM,add_zero];rfl
  | @advance j T ih => exact ih σ (H+L j (finiteGaussianLeft z)) (finiteGaussianRight z)
  | fork T U ihT ihU =>
      exact congrArg₂ (fun x y : ℝ=>x+y)
        (ihT σ.1 H (finiteGaussianLeft z)) (ihU σ.2 H (finiteGaussianRight z))

end FourPapersCommon
