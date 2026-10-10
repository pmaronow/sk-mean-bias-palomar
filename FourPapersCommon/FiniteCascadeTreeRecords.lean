module
public import FourPapersCommon.FiniteCascadeGenealogy
public import Mathlib.Probability.Kernel.Composition.KernelLemmas

@[expose] public section

/-! Full field records of a finite marked Gaussian genealogy. Leaves are
terminal Gibbs spins; every edge records its genuine normalized Gaussian
continuation, and branches are conditionally independent. The spin marginal
is the previously constructed actual genealogy law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteCascadeGenealogy

inductive FiniteTerminalGenealogy : ℕ → Type
  | leaf : FiniteTerminalGenealogy 0
  | advance {j : ℕ} : FiniteTerminalGenealogy j → FiniteTerminalGenealogy (j+1)
  | fork {j : ℕ} : FiniteTerminalGenealogy j → FiniteTerminalGenealogy j →
      FiniteTerminalGenealogy j

namespace FiniteTerminalGenealogy

@[reducible] def asGenealogy : {j : ℕ} → FiniteTerminalGenealogy j → FiniteCascadeGenealogy j
  | _, .leaf => .leaf 0
  | _, .advance T => .advance (asGenealogy T)
  | _, .fork T U => .fork (asGenealogy T) (asGenealogy U)

@[reducible] def Records (E S : Type) : {j : ℕ} → FiniteTerminalGenealogy j → Type _
  | _, .leaf => S
  | _, .advance T => E × Records E S T
  | _, .fork T U => Records E S T × Records E S U

@[reducible] def recordMeasurableSpace (E S : Type) [MeasurableSpace E] [MeasurableSpace S] :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → MeasurableSpace (Records E S T)
  | _, .leaf => inferInstanceAs (MeasurableSpace S)
  | _, .advance T => @Prod.instMeasurableSpace _ _ inferInstance (recordMeasurableSpace E S T)
  | _, .fork T U => @Prod.instMeasurableSpace _ _
      (recordMeasurableSpace E S T) (recordMeasurableSpace E S U)

instance {E S : Type} [MeasurableSpace E] [MeasurableSpace S] {j : ℕ}
    (T : FiniteTerminalGenealogy j) : MeasurableSpace (Records E S T) :=
  recordMeasurableSpace E S T

@[reducible] def spins {E S : Type} : {j : ℕ} → (T : FiniteTerminalGenealogy j) →
    Records E S T → Samples S (asGenealogy T)
  | _, .leaf => id
  | _, .advance T => spins (E:=E) (S:=S) T ∘ Prod.snd
  | _, .fork T U => Prod.map (spins (E:=E) (S:=S) T) (spins (E:=E) (S:=S) U)

theorem measurable_spins {E S : Type} [MeasurableSpace E] [MeasurableSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) : Measurable (spins (E:=E) (S:=S) T) := by
  induction T with
  | leaf => exact measurable_id
  | advance T ih => exact ih.comp measurable_snd
  | fork T U ihT ihU => exact ihT.prodMap ihU

end FiniteTerminalGenealogy

open FiniteTerminalGenealogy
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

@[reducible] def finiteCascadeTreeRecordKernel (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) →
      Kernel (FiniteStateField S) (Records (FiniteStateField S) S T)
  | _, .leaf => finiteStateGibbsKernel V
  | _, @FiniteTerminalGenealogy.advance j T =>
      (Kernel.id ×ₖ finiteCascadeTreeRecordKernel V a L T) ∘ₖ
        finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j
  | _, .fork T U => finiteCascadeTreeRecordKernel V a L T ×ₖ finiteCascadeTreeRecordKernel V a L U

theorem isMarkovKernel_finiteCascadeTreeRecordKernel (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    IsMarkovKernel (finiteCascadeTreeRecordKernel V a L T) := by
  induction T with
  | leaf => exact isMarkovKernel_finiteStateGibbsKernel V
  | @advance j T ih =>
      haveI := ih
      haveI := isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L j
      change IsMarkovKernel ((_ ×ₖ _) ∘ₖ _)
      infer_instance
  | fork T U ihT ihU =>
      haveI := ihT
      haveI := ihU
      change IsMarkovKernel (_ ×ₖ _)
      infer_instance

theorem finiteCascadeTreeRecordKernel_spin_marginal (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (finiteCascadeTreeRecordKernel V a L T).map (spins T) =
      finiteCascadeGenealogyKernel V a L (asGenealogy T) := by
  induction T with
  | leaf =>
      simp only [finiteCascadeTreeRecordKernel,spins,Kernel.map_id,asGenealogy,
        finiteCascadeGenealogyKernel,finiteStateCascadeGibbsKernel,
        finiteStateCascadeFieldKernel,OverlapPaper.sourceKernelLaw,Kernel.comp_id]
  | @advance j T ih =>
      haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
      change ((_ ×ₖ _) ∘ₖ _).map (spins T ∘ Prod.snd) = _ ∘ₖ _
      rw [Kernel.map_comp,Kernel.map_comp_right _ measurable_snd (measurable_spins T),
        ←Kernel.snd_eq,Kernel.snd_prod,ih]
  | fork T U ihT ihU =>
      haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
      haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L U
      change (_ ×ₖ _).map (Prod.map (spins T) (spins U)) = _ ×ₖ _
      rw [←Kernel.map_prod_map _ _ (measurable_spins T) (measurable_spins U),ihT,ihU]

end FourPapersCommon
