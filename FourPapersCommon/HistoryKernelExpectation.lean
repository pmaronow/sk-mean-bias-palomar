module
public import FourPapersCommon.HistoryInitial
public import OverlapPaper.ReplicaSourceBranchingEstimate

@[expose] public section

/-! Bounded kernel expectations in reverse recursion order are genuine
expectations of the chronologically constructed finite Markov history. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
open OverlapPaper
variable {A : Type*} [MeasurableSpace A]
set_option maxHeartbeats 1200000

theorem integral_history_backward_at_initial_up_to
    (ν : Measure A) [IsProbabilityMeasure ν] (κ : ℕ→Kernel A A)
    (hκ : ∀j,IsMarkovKernel (κ j)) (f : ℕ→A→ℝ)
    (hf : ∀j,Measurable (f j)) (C : ℝ) (hb : ∀j x,|f j x|≤C)
    (N : ℕ) (hback : ∀j<N,∀x,f j x=∫y,f (j+1) y∂κ j x) :
    (∫h,f N (h (Fin.last N))∂finiteHistoryLaw ν κ N)=∫x,f 0 x∂ν := by
  induction N with
  | zero =>
    rw [finiteHistoryLaw]
    exact integral_map (by fun_prop) ((hf 0).comp (measurable_pi_apply 0)).aestronglyMeasurable
  | succ N ih =>
    have hstep:=integral_history_observation_step ν κ hκ N 0 (Nat.zero_le _)
      (fun _=>1) (f (N+1)) measurable_const (hf _) 1 C (by simp) (hb _)
    simp only [one_mul] at hstep
    rw [hstep]
    simp_rw [←hback N (by omega)]
    exact ih (fun j hj=>hback j (by omega))

theorem integral_history_eq_reverse_kernel_expectation
    (ν : Measure A) [IsProbabilityMeasure ν] (κ : ℕ→Kernel A A)
    (hκ : ∀j,IsMarkovKernel (κ j)) (N : ℕ) (F : A→ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hb : ∀x,|F x|≤C) :
    (∫h,F (h (Fin.last N))∂finiteHistoryLaw ν κ N)=
      ∫x,sourceKernelExpectation (fun j=>κ (N-1-j)) N F x∂ν := by
  let Q:=fun j=>κ (N-1-j)
  let f:=fun i=>sourceKernelExpectation Q (N-i) F
  have hf i : Measurable (f i):=sourceKernelExpectation_measurable Q F hF _
  have hb' i x : |f i x|≤C:=sourceKernelExpectation_abs_le Q (fun j=>hκ _) F hF C hC hb _ x
  have hback i (hi : i<N) x : f i x=∫y,f (i+1) y∂κ i x := by
    have he : N-i=(N-(i+1))+1:=by omega
    have hi' : N-1-(N-(i+1))=i:=by omega
    simp only [f,he,sourceKernelExpectation,Q,hi']
  simpa only [f,Nat.sub_self,Nat.sub_zero,sourceKernelExpectation] using
    integral_history_backward_at_initial_up_to ν κ hκ f hf C hb' N hback

end FourPapersCommon
