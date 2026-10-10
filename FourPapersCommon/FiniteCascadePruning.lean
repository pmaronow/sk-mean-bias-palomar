module
public import FourPapersCommon.FiniteCascadeGenealogy

@[expose] public section

/-! Deleting descendants from an actual normalized Gaussian cascade tree.
The projections are explicit measurable maps and the marginal law is the
law of the retained tree, including all its shared transitions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteCascadeGenealogy

inductive FiniteCascadePruning : {j : ℕ} →
    FiniteCascadeGenealogy j → FiniteCascadeGenealogy j → Type
  | refl {j : ℕ} (T : FiniteCascadeGenealogy j) : FiniteCascadePruning T T
  | advance {j : ℕ} {T U : FiniteCascadeGenealogy j} : FiniteCascadePruning T U →
      FiniteCascadePruning (.advance T) (.advance U)
  | fork {j : ℕ} {T₁ T₂ U₁ U₂ : FiniteCascadeGenealogy j} :
      FiniteCascadePruning T₁ U₁ → FiniteCascadePruning T₂ U₂ →
      FiniteCascadePruning (.fork T₁ T₂) (.fork U₁ U₂)
  | left {j : ℕ} {T U : FiniteCascadeGenealogy j} (W : FiniteCascadeGenealogy j) :
      FiniteCascadePruning T U → FiniteCascadePruning (.fork T W) U
  | right {j : ℕ} {T U : FiniteCascadeGenealogy j} (W : FiniteCascadeGenealogy j) :
      FiniteCascadePruning T U → FiniteCascadePruning (.fork W T) U

namespace FiniteCascadePruning

@[reducible] def project {S : Type*} : {j : ℕ} →
    {T U : FiniteCascadeGenealogy j} → FiniteCascadePruning T U → Samples S T → Samples S U
  | _, _, _, .refl _ => id
  | _, _, _, @FiniteCascadePruning.advance j T U P =>
      project (S:=S) (T:=T) (U:=U) P
  | _, _, _, @FiniteCascadePruning.fork j T₁ T₂ U₁ U₂ P Q =>
      Prod.map (project (S:=S) (T:=T₁) (U:=U₁) P)
        (project (S:=S) (T:=T₂) (U:=U₂) Q)
  | _, _, _, @FiniteCascadePruning.left j T U W P =>
      project (S:=S) (T:=T) (U:=U) P ∘ Prod.fst
  | _, _, _, @FiniteCascadePruning.right j T U W P =>
      project (S:=S) (T:=T) (U:=U) P ∘ Prod.snd

theorem measurable_project {S : Type*} [MeasurableSpace S] {j : ℕ}
    {T U : FiniteCascadeGenealogy j} (P : FiniteCascadePruning T U) :
    Measurable (project (S:=S) P) := by
  induction P with
  | refl T => exact measurable_id
  | advance P ih => exact ih
  | fork P Q ihP ihQ => exact ihP.prodMap ihQ
  | left W P ih => exact ih.comp measurable_fst
  | right W P ih => exact ih.comp measurable_snd

end FiniteCascadePruning

open FiniteCascadePruning
open SpinGlass.AT
variable {S I : Type*} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem finiteCascadeGenealogyKernel_pruning (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T U : FiniteCascadeGenealogy j} (P : FiniteCascadePruning T U) :
    (finiteCascadeGenealogyKernel V a L T).map (project P) =
      finiteCascadeGenealogyKernel V a L U := by
  induction P with
  | refl T => exact Kernel.map_id _
  | advance P ih =>
      change (_ ∘ₖ _).map (project P) = _ ∘ₖ _
      rw [Kernel.map_comp,ih]
  | @fork j T₁ T₂ U₁ U₂ P Q ihP ihQ =>
      haveI := isMarkovKernel_finiteCascadeGenealogyKernel V a ha L T₁
      haveI := isMarkovKernel_finiteCascadeGenealogyKernel V a ha L T₂
      change (_ ×ₖ _).map (Prod.map (project P) (project Q)) = _ ×ₖ _
      rw [←Kernel.map_prod_map _ _ (measurable_project P) (measurable_project Q),ihP,ihQ]
  | @left j T U W P ih =>
      haveI := isMarkovKernel_finiteCascadeGenealogyKernel V a ha L T
      haveI := isMarkovKernel_finiteCascadeGenealogyKernel V a ha L W
      change (_ ×ₖ _).map (project P ∘ Prod.fst) = _
      rw [Kernel.map_comp_right _ measurable_fst (measurable_project P),
        ←Kernel.fst_eq,Kernel.fst_prod,ih]
  | @right j T U W P ih =>
      haveI := isMarkovKernel_finiteCascadeGenealogyKernel V a ha L T
      haveI := isMarkovKernel_finiteCascadeGenealogyKernel V a ha L W
      change (_ ×ₖ _).map (project P ∘ Prod.snd) = _
      rw [Kernel.map_comp_right _ measurable_snd (measurable_project P),
        ←Kernel.snd_eq,Kernel.snd_prod,ih]

end FourPapersCommon
