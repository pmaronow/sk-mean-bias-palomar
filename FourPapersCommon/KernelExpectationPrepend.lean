module
public import OverlapPaper.ReplicaSourceMarkovRecursion

@[expose] public section

/-! Exact removal of the innermost normalized transition from a finite
nonstationary future-kernel expectation. No Fubini or moment premise is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open OverlapPaper
variable {A : Type*} [MeasurableSpace A]

theorem sourceKernelExpectation_prepend (Q : ℕ → Kernel A A) (p q : ℕ)
    (F : A → ℝ) (x : A) :
    sourceKernelExpectation (fun j => Q (p+j)) (q+1) F x =
      sourceKernelExpectation (fun j => Q (p+1+j)) q (fun y => ∫z, F z ∂Q p y) x := by
  induction q generalizing x with
  | zero => simp only [sourceKernelExpectation, add_zero]
  | succ q ih =>
    change (∫y, sourceKernelExpectation (fun j => Q (p+j)) (q+1) F y
      ∂Q (p+(q+1)) x) =
      ∫y, sourceKernelExpectation (fun j => Q (p+1+j)) q
        (fun y => ∫z, F z ∂Q p y) y ∂Q (p+1+q) x
    rw [show p+(q+1)=p+1+q by omega]
    apply integral_congr_ae
    exact .of_forall ih

end FourPapersCommon
