module
public import FourPapersCommon.FiniteObservationTreeTopology

@[expose] public section

/-! Explicit deletion of branches from complete observation records.
Every retained edge keeps its field, and the pushed-forward law is exactly
that of the smaller actual Markov genealogy. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

inductive FiniteObservationPruning : {j : ℕ} →
    FiniteTerminalGenealogy j → FiniteTerminalGenealogy j → Type
  | refl {j : ℕ} (T : FiniteTerminalGenealogy j) : FiniteObservationPruning T T
  | advance {j : ℕ} {T U : FiniteTerminalGenealogy j} : FiniteObservationPruning T U →
      FiniteObservationPruning (.advance T) (.advance U)
  | fork {j : ℕ} {T₁ T₂ U₁ U₂ : FiniteTerminalGenealogy j} :
      FiniteObservationPruning T₁ U₁ → FiniteObservationPruning T₂ U₂ →
      FiniteObservationPruning (.fork T₁ T₂) (.fork U₁ U₂)
  | left {j : ℕ} {T U : FiniteTerminalGenealogy j} (W : FiniteTerminalGenealogy j) :
      FiniteObservationPruning T U → FiniteObservationPruning (.fork T W) U
  | right {j : ℕ} {T U : FiniteTerminalGenealogy j} (W : FiniteTerminalGenealogy j) :
      FiniteObservationPruning T U → FiniteObservationPruning (.fork W T) U

namespace FiniteObservationPruning
@[reducible] def project {E S : Type} : {j : ℕ} →
    {T U : FiniteTerminalGenealogy j} → FiniteObservationPruning T U →
      Records E S T → Records E S U
  | _, _, _, .refl _ => id
  | _, _, _, @FiniteObservationPruning.advance j T U P =>
      Prod.map id (project (E:=E) (S:=S) P)
  | _, _, _, @FiniteObservationPruning.fork j T₁ T₂ U₁ U₂ P Q =>
      Prod.map (project (E:=E) (S:=S) P) (project (E:=E) (S:=S) Q)
  | _, _, _, @FiniteObservationPruning.left j T U W P =>
      project (E:=E) (S:=S) P ∘ Prod.fst
  | _, _, _, @FiniteObservationPruning.right j T U W P =>
      project (E:=E) (S:=S) P ∘ Prod.snd

theorem measurable_project {E S : Type} [MeasurableSpace E] [MeasurableSpace S] {j : ℕ}
    {T U : FiniteTerminalGenealogy j} (P : FiniteObservationPruning T U) :
    Measurable (project (E:=E) (S:=S) P) := by
  induction P with
  | refl T => exact measurable_id
  | advance P ih => exact measurable_id.prodMap ih
  | fork P Q ihP ihQ => exact ihP.prodMap ihQ
  | left W P ih => exact ih.comp measurable_fst
  | right W P ih => exact ih.comp measurable_snd

theorem continuous_project {E S : Type} [TopologicalSpace E] [TopologicalSpace S] {j : ℕ}
    {T U : FiniteTerminalGenealogy j} (P : FiniteObservationPruning T U) :
    Continuous (project (E:=E) (S:=S) P) := by
  induction P with
  | refl T => exact continuous_id
  | advance P ih => exact continuous_id.prodMap ih
  | fork P Q ihP ihQ => exact ihP.prodMap ihQ
  | left W P ih => exact ih.comp continuous_fst
  | right W P ih => exact ih.comp continuous_snd
end FiniteObservationPruning
open FiniteObservationPruning

variable {E S : Type} [MeasurableSpace E] [MeasurableSpace S]
theorem observationTreeKernel_pruning (κ : ℕ→Kernel E E) (hκ : ∀j,IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ] {j : ℕ} {T U : FiniteTerminalGenealogy j}
    (P : FiniteObservationPruning T U) :
    (observationTreeKernel κ θ T).map (project P)=observationTreeKernel κ θ U := by
  induction P with
  | refl T => exact Kernel.map_id _
  | @advance j T U P ih =>
      haveI:=observationTreeKernel_markov κ hκ θ T
      haveI:=hκ j
      change ((_ ×ₖ _) ∘ₖ _).map (Prod.map id (project P))=(_ ×ₖ _) ∘ₖ _
      rw [Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id (measurable_project P),
        Kernel.map_id,ih]
  | @fork j T₁ T₂ U₁ U₂ P Q ihP ihQ =>
      haveI:=observationTreeKernel_markov κ hκ θ T₁
      haveI:=observationTreeKernel_markov κ hκ θ T₂
      change (_ ×ₖ _).map (Prod.map (project P) (project Q))=_ ×ₖ _
      rw [←Kernel.map_prod_map _ _ (measurable_project P) (measurable_project Q),ihP,ihQ]
  | @left j T U W P ih =>
      haveI:=observationTreeKernel_markov κ hκ θ T
      haveI:=observationTreeKernel_markov κ hκ θ W
      change (_ ×ₖ _).map (project P ∘ Prod.fst)=_
      rw [Kernel.map_comp_right _ measurable_fst (measurable_project P),
        ←Kernel.fst_eq,Kernel.fst_prod,ih]
  | @right j T U W P ih =>
      haveI:=observationTreeKernel_markov κ hκ θ T
      haveI:=observationTreeKernel_markov κ hκ θ W
      change (_ ×ₖ _).map (project P ∘ Prod.snd)=_
      rw [Kernel.map_comp_right _ measurable_snd (measurable_project P),
        ←Kernel.snd_eq,Kernel.snd_prod,ih]

theorem observationJointLaw_pruning (κ : ℕ→Kernel E E) (hκ : ∀j,IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ] (ν : Measure E) [SFinite ν]
    {j : ℕ} {T U : FiniteTerminalGenealogy j} (P : FiniteObservationPruning T U) :
    (ν ⊗ₘ observationTreeKernel κ θ T).map (Prod.map id (project P))=
      ν ⊗ₘ observationTreeKernel κ θ U := by
  haveI:=observationTreeKernel_markov κ hκ θ T
  rw [←Measure.compProd_map (measurable_project P),observationTreeKernel_pruning κ hκ θ P]

end FourPapersCommon
