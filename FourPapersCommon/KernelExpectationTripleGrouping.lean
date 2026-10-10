module
public import OverlapPaper.ReplicaSourceBranchingEstimate

@[expose] public section

/-! Actual grouping of three consecutive Markov transitions, retaining their
full state law and every bounded measurable observable. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open OverlapPaper
variable {E : Type*} [MeasurableSpace E]
set_option maxHeartbeats 800000

def tripleGroupedKernel (Q : ℕ→Kernel E E) (j : ℕ) : Kernel E E :=
  (Q (3*j) ∘ₖ Q (3*j+1)) ∘ₖ Q (3*j+2)

theorem tripleGroupedKernel_markov (Q : ℕ→Kernel E E)
    (hQ : ∀j,IsMarkovKernel (Q j)) (j : ℕ) :
    IsMarkovKernel (tripleGroupedKernel Q j) := by
  letI:=hQ (3*j)
  letI:=hQ (3*j+1)
  letI:=hQ (3*j+2)
  unfold tripleGroupedKernel
  infer_instance

theorem sourceKernelLaw_triple_group (Q : ℕ→Kernel E E)
    (hQ : ∀j,IsMarkovKernel (Q j)) (J : ℕ) :
    sourceKernelLaw (tripleGroupedKernel Q) J=sourceKernelLaw Q (3*J) := by
  induction J with
  | zero => rfl
  | succ J ih =>
    letI:=isMarkovKernel_sourceKernelLaw Q hQ (3*J)
    letI:=hQ (3*J)
    letI:=hQ (3*J+1)
    letI:=hQ (3*J+2)
    rw [sourceKernelLaw,ih,tripleGroupedKernel,
      show 3*(J+1)=((3*J+1)+1)+1 by omega]
    rw [sourceKernelLaw,sourceKernelLaw,sourceKernelLaw]
    simp only [Kernel.comp_assoc]

theorem sourceKernelExpectation_triple_group (Q : ℕ→Kernel E E)
    (hQ : ∀j,IsMarkovKernel (Q j)) (F : E→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀x,|F x|≤C) (J : ℕ) (x : E) :
    sourceKernelExpectation Q (3*J) F x=
      sourceKernelExpectation (tripleGroupedKernel Q) J F x := by
  rw [sourceKernelExpectation_eq_integral Q hQ F hF C hC,
    sourceKernelExpectation_eq_integral (tripleGroupedKernel Q)
      (tripleGroupedKernel_markov Q hQ) F hF C hC,sourceKernelLaw_triple_group Q hQ]

end FourPapersCommon
