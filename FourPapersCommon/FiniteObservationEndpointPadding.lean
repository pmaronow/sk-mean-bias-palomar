module
public import FourPapersCommon.FiniteObservationTreeTransport

@[expose] public section

/-! Adding an identity observation immediately above every terminal leaf
preserves the complete old record law. All original transitions shift by
one index; the new terminal transition is the actual identity kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def observationTerminalUnaryLift : {j : ℕ} →
    FiniteTerminalGenealogy j → FiniteTerminalGenealogy (j+1)
  | _, .leaf => .advance .leaf
  | _, .advance T => .advance (observationTerminalUnaryLift T)
  | _, .fork T U => .fork (observationTerminalUnaryLift T) (observationTerminalUnaryLift U)

@[reducible] def observationTerminalUnaryProject {E S : Type} : {j : ℕ} →
    (T : FiniteTerminalGenealogy j) → Records E S (observationTerminalUnaryLift T) → Records E S T
  | _, .leaf => Prod.snd
  | _, .advance T => Prod.map id (observationTerminalUnaryProject T)
  | _, .fork T U => Prod.map (observationTerminalUnaryProject T) (observationTerminalUnaryProject U)

theorem measurable_observationTerminalUnaryProject {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S] {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (observationTerminalUnaryProject (E:=E) (S:=S) T) := by
  induction T with
  | leaf => exact measurable_snd
  | advance T ih => exact measurable_id.prodMap ih
  | fork T U ihT ihU => exact ihT.prodMap ihU

@[reducible] def observationTerminalUnaryKernels {E : Type} [MeasurableSpace E]
    (κ : ℕ → Kernel E E) : ℕ → Kernel E E
  | 0 => Kernel.id
  | j+1 => κ j

theorem observationTerminalUnaryKernels_markov {E : Type} [MeasurableSpace E]
    (κ : ℕ → Kernel E E) (hκ : ∀j, IsMarkovKernel (κ j)) :
    ∀j, IsMarkovKernel (observationTerminalUnaryKernels κ j) := by
  intro j
  cases j with
  | zero => exact inferInstance
  | succ j => exact hκ j

theorem observationTreeKernel_terminalUnaryLift {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S]
    (κ : ℕ → Kernel E E) (hκ : ∀j, IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ] {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (observationTreeKernel (observationTerminalUnaryKernels κ) θ (observationTerminalUnaryLift T)).map
      (observationTerminalUnaryProject T) = observationTreeKernel κ θ T := by
  induction T with
  | leaf =>
      change ((Kernel.id ×ₖ θ) ∘ₖ Kernel.id).map Prod.snd = θ
      rw [Kernel.comp_id,←Kernel.snd_eq,Kernel.snd_prod]
  | @advance j T ih =>
      haveI := observationTreeKernel_markov (observationTerminalUnaryKernels κ)
        (observationTerminalUnaryKernels_markov κ hκ) θ (observationTerminalUnaryLift T)
      haveI := hκ j
      change ((_ ×ₖ _) ∘ₖ κ j).map (Prod.map id (observationTerminalUnaryProject T)) =
        (Kernel.id ×ₖ observationTreeKernel κ θ T) ∘ₖ κ j
      rw [Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
        (measurable_observationTerminalUnaryProject T),Kernel.map_id,ih]
  | fork T U ihT ihU =>
      haveI := observationTreeKernel_markov (observationTerminalUnaryKernels κ)
        (observationTerminalUnaryKernels_markov κ hκ) θ (observationTerminalUnaryLift T)
      haveI := observationTreeKernel_markov (observationTerminalUnaryKernels κ)
        (observationTerminalUnaryKernels_markov κ hκ) θ (observationTerminalUnaryLift U)
      change (_ ×ₖ _).map (Prod.map (observationTerminalUnaryProject T)
        (observationTerminalUnaryProject U)) = _ ×ₖ _
      rw [←Kernel.map_prod_map _ _ (measurable_observationTerminalUnaryProject T)
        (measurable_observationTerminalUnaryProject U),ihT,ihU]

theorem observationJointLaw_terminalUnaryLift {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S]
    (κ : ℕ → Kernel E E) (hκ : ∀j, IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ] (ν : Measure E) [SFinite ν]
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (ν ⊗ₘ observationTreeKernel (observationTerminalUnaryKernels κ) θ (observationTerminalUnaryLift T)).map
      (Prod.map id (observationTerminalUnaryProject T)) = ν ⊗ₘ observationTreeKernel κ θ T := by
  haveI := observationTreeKernel_markov (observationTerminalUnaryKernels κ)
    (observationTerminalUnaryKernels_markov κ hκ) θ (observationTerminalUnaryLift T)
  rw [←Measure.compProd_map (measurable_observationTerminalUnaryProject T),
    observationTreeKernel_terminalUnaryLift κ hκ θ T]

end FourPapersCommon
