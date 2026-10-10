module
public import FourPapersCommon.HistoryInitial

@[expose] public section

/-! The endpoint backward identity needs the actual transition equations
only up to the finite last observation, not after the history has ended. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
variable {State : Type*} [MeasurableSpace State]

theorem integral_history_backward_at_initial_upto (ν : Measure State) [IsProbabilityMeasure ν]
    (κ : ℕ→Kernel State State) (hκ : ∀i,IsMarkovKernel (κ i)) (N : ℕ)
    (f : ℕ→State→ℝ) (hf : ∀i,i≤N→Measurable (f i))
    (R : ℝ) (hR : ∀i,i≤N→∀x,|f i x|≤R)
    (hb : ∀i,i<N→∀x,f i x=∫y,f (i+1) y ∂κ i x) :
    (∫h,f N (h (Fin.last N)) ∂finiteHistoryLaw ν κ N)=∫x,f 0 x ∂ν := by
  induction N with
  | zero=>
    exact integral_map (by fun_prop : AEMeasurable (fun x : State=>fun _ : Fin 1=>x) ν)
      ((hf 0 le_rfl).comp (measurable_pi_apply (Fin.last 0))).aestronglyMeasurable
  | succ N ih=>
    have hh := integral_history_observation_step ν κ hκ N 0 (Nat.zero_le _)
      (fun _=>1) (f (N+1)) measurable_const (hf _ le_rfl) 1 R
      (fun _=>by norm_num) (hR _ le_rfl)
    simp only [one_mul] at hh
    rw [hh]
    simp_rw [←hb N (Nat.lt_succ_self _)]
    exact ih (fun i hi=>hf i (hi.trans (Nat.le_succ _)))
      (fun i hi=>hR i (hi.trans (Nat.le_succ _)))
      (fun i hi=>hb i (hi.trans (Nat.lt_succ_self _)))

end FourPapersCommon
