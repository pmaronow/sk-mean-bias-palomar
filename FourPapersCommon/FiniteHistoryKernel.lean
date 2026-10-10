module
public import FourPapersCommon.FiniteHistory
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section

/-! The chronological history itself is a genuine Markov kernel of the
 initial point. Integrating this kernel against an initial law gives the
 actual finite-history law, allowing honest mixing of fixed-parameter laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
variable {State : Type*} [MeasurableSpace State]

def finiteHistoryKernel (κ : ℕ→Kernel State State) :
    (j : ℕ)→Kernel State (FiniteHistory State j)
  | 0 => Kernel.deterministic (fun x _=>x) (by fun_prop)
  | j+1 => (((Kernel.id : Kernel (FiniteHistory State j) (FiniteHistory State j))×ₖ
      (κ j).comap (fun h=>h (Fin.last j)) (measurable_pi_apply _)).map (historySplit j).symm)∘ₖ
      finiteHistoryKernel κ j

theorem finiteHistoryKernel_markov (κ : ℕ→Kernel State State)
    (hκ : ∀j,IsMarkovKernel (κ j)) (j : ℕ) : IsMarkovKernel (finiteHistoryKernel κ j) := by
  induction j with
  | zero => unfold finiteHistoryKernel;infer_instance
  | succ j ih =>
    letI:=hκ j
    letI:=ih
    unfold finiteHistoryKernel
    haveI := Kernel.IsMarkovKernel.map
      ((Kernel.id : Kernel (FiniteHistory State j) (FiniteHistory State j))×ₖ
        (κ j).comap (fun h=>h (Fin.last j)) (measurable_pi_apply _))
      (historySplit j).symm.measurable
    infer_instance

theorem finiteHistoryKernel_comp (ν : Measure State) [IsProbabilityMeasure ν]
    (κ : ℕ→Kernel State State) (hκ : ∀j,IsMarkovKernel (κ j)) (j : ℕ) :
    (finiteHistoryKernel κ j)∘ₘν=finiteHistoryLaw ν κ j := by
  induction j with
  | zero => simp only [finiteHistoryKernel,finiteHistoryLaw,Measure.deterministic_comp_eq_map]
  | succ j ih =>
    letI:=hκ j
    letI:=finiteHistoryKernel_markov κ hκ j
    letI:=isProbabilityMeasure_finiteHistoryLaw ν κ hκ j
    change ((((Kernel.id : Kernel (FiniteHistory State j) (FiniteHistory State j))×ₖ
      (κ j).comap (fun h=>h (Fin.last j)) (measurable_pi_apply _)).map (historySplit j).symm)∘ₖ
      finiteHistoryKernel κ j)∘ₘν=_
    rw [←Measure.comp_assoc,ih,←Measure.map_comp _ _ (historySplit j).symm.measurable,
      ←Measure.compProd_eq_comp_prod]
    rfl

theorem finiteHistoryKernel_apply (κ : ℕ→Kernel State State)
    (hκ : ∀j,IsMarkovKernel (κ j)) (j : ℕ) (x : State) :
    finiteHistoryKernel κ j x=finiteHistoryLaw (Measure.dirac x) κ j := by
  rw [←finiteHistoryKernel_comp (Measure.dirac x) κ hκ j]
  exact (Measure.dirac_bind (finiteHistoryKernel κ j).measurable x).symm

end FourPapersCommon
