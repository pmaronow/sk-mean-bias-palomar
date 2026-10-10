module
public import FourPapersCommon.FiniteStateCascadeGibbs
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.CompMap

@[expose] public section

/-! Actual finite Gaussian-cascade genealogies. An advance uses the genuine
normalized Cole--Hopf transition, and a fork samples independent continuations
from the common field. Every descendant has the original terminal spin law.
Pruning is proved at the level of probability kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon

inductive FiniteCascadeGenealogy : ℕ → Type
  | leaf (j : ℕ) : FiniteCascadeGenealogy j
  | advance {j : ℕ} : FiniteCascadeGenealogy j → FiniteCascadeGenealogy (j+1)
  | fork {j : ℕ} : FiniteCascadeGenealogy j → FiniteCascadeGenealogy j →
      FiniteCascadeGenealogy j

namespace FiniteCascadeGenealogy

@[reducible] def Samples (S : Type*) : {j : ℕ} → FiniteCascadeGenealogy j → Type _
  | _, .leaf _ => S
  | _, .advance T => Samples S T
  | _, .fork T U => Samples S T × Samples S U

@[reducible] def Leaf : {j : ℕ} → FiniteCascadeGenealogy j → Type
  | _, .leaf _ => Unit
  | _, .advance T => Leaf T
  | _, .fork T U => Leaf T ⊕ Leaf U

@[reducible] def sampleMeasurableSpace (S : Type*) [MeasurableSpace S] :
    {j : ℕ} → (T : FiniteCascadeGenealogy j) → MeasurableSpace (Samples S T)
  | _, .leaf _ => inferInstanceAs (MeasurableSpace S)
  | _, .advance T => sampleMeasurableSpace S T
  | _, .fork T U => @Prod.instMeasurableSpace _ _
      (sampleMeasurableSpace S T) (sampleMeasurableSpace S U)

instance {S : Type*} [MeasurableSpace S] {j : ℕ} (T : FiniteCascadeGenealogy j) :
    MeasurableSpace (Samples S T) := sampleMeasurableSpace S T

@[reducible] def eval {S : Type*} : {j : ℕ} → (T : FiniteCascadeGenealogy j) →
    Leaf T → Samples S T → S
  | _, .leaf _ => fun _ σ => σ
  | _, .advance T => eval T
  | _, .fork T U => fun i σ => Sum.elim (fun l => eval T l σ.1)
      (fun r => eval U r σ.2) i

theorem measurable_eval {S : Type*} [MeasurableSpace S] {j : ℕ}
    (T : FiniteCascadeGenealogy j) (i : Leaf T) : Measurable (eval (S:=S) T i) := by
  induction T with
  | leaf j => exact measurable_id
  | advance T ih => exact ih i
  | fork T U ihT ihU =>
      cases i with
      | inl i => exact (ihT i).comp measurable_fst
      | inr i => exact (ihU i).comp measurable_snd

def leafCount : {j : ℕ} → FiniteCascadeGenealogy j → ℕ
  | _, .leaf _ => 1
  | _, .advance T => leafCount T
  | _, .fork T U => leafCount T + leafCount U

theorem leafCount_pos {j : ℕ} (T : FiniteCascadeGenealogy j) : 0 < leafCount T := by
  induction T with
  | leaf j => exact Nat.zero_lt_one
  | advance T ih => exact ih
  | fork T U ihT ihU => change 0 < leafCount T + leafCount U; omega

end FiniteCascadeGenealogy

open FiniteCascadeGenealogy
open SpinGlass.AT OverlapPaper
variable {S I : Type*} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

@[reducible] def finiteCascadeGenealogyKernel (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    {j : ℕ} → (T : FiniteCascadeGenealogy j) →
      Kernel (FiniteStateField S) (Samples S T)
  | _, .leaf j => finiteStateCascadeGibbsKernel V a L j
  | _, @FiniteCascadeGenealogy.advance j T => finiteCascadeGenealogyKernel V a L T ∘ₖ
      finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j
  | _, .fork T U => finiteCascadeGenealogyKernel V a L T ×ₖ
      finiteCascadeGenealogyKernel V a L U

theorem isMarkovKernel_finiteCascadeGenealogyKernel (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteCascadeGenealogy j) :
    IsMarkovKernel (finiteCascadeGenealogyKernel V a L T) := by
  induction T with
  | leaf j => exact isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L j
  | @advance j T ih =>
      haveI := ih
      haveI := isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L j
      change IsMarkovKernel (_ ∘ₖ _)
      infer_instance
  | fork T U ihT ihU =>
      haveI := ihT
      haveI := ihU
      change IsMarkovKernel (_ ×ₖ _)
      infer_instance

theorem finiteStateCascadeGibbsKernel_succ (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    finiteStateCascadeGibbsKernel V a L (j+1) =
      finiteStateCascadeGibbsKernel V a L j ∘ₖ
        finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j := by
  simp only [finiteStateCascadeGibbsKernel,finiteStateCascadeFieldKernel,
    sourceKernelLaw,Kernel.comp_assoc]

theorem finiteCascadeGenealogyKernel_leaf_marginal (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteCascadeGenealogy j) (i : Leaf T) :
    (finiteCascadeGenealogyKernel V a L T).map (eval T i) =
      finiteStateCascadeGibbsKernel V a L j := by
  induction T with
  | leaf j => exact Kernel.map_id _
  | @advance j T ih =>
      change (_ ∘ₖ _).map (eval T i) = _
      rw [Kernel.map_comp,ih i,←finiteStateCascadeGibbsKernel_succ]
  | fork T U ihT ihU =>
      haveI := isMarkovKernel_finiteCascadeGenealogyKernel V a ha L T
      haveI := isMarkovKernel_finiteCascadeGenealogyKernel V a ha L U
      cases i with
      | inl i =>
          change (_ ×ₖ _).map (eval T i ∘ Prod.fst) = _
          rw [Kernel.map_comp_right _ measurable_fst (measurable_eval T i)]
          rw [←Kernel.fst_eq,Kernel.fst_prod,ihT i]
      | inr i =>
          change (_ ×ₖ _).map (eval U i ∘ Prod.snd) = _
          rw [Kernel.map_comp_right _ measurable_snd (measurable_eval U i)]
          rw [←Kernel.snd_eq,Kernel.snd_prod,ihU i]

end FourPapersCommon
