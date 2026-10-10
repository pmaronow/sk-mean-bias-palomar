module
public import FourPapersCommon.FiniteStateSameMassResponses

@[expose] public section

/-! Genuine signed active directions in a same-mass threefold covariance
schedule. The decreasing/increasing base copies cancel, while either sign
of the third direction is retained in the actual normalized response. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
set_option maxHeartbeats 1500000
variable {S I : Type*} [Fintype S] [Fintype I] [DecidableEq I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

private theorem sum_range_three_signed {E : Type*} [AddCommMonoid E] (f : ℕ→E) (n : ℕ) :
    (∑j∈Finset.range (3*n),f j)=
      ∑i∈Finset.range n,(f (3*i)+f (3*i+1)+f (3*i+2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3*(n+1)=((3*n+1)+1)+1 by omega]
    rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,ih,
      Finset.sum_range_succ]
    ac_rfl

theorem finiteStateGaussianScheduledTerminal_time_signed_threefold
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (A : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (up : ℕ→Bool) (N : ℕ)
    (hup : ∀i<N,up (3*i)=false ∧ up (3*i+1)=true)
    (hm : ∀i<N,a (3*i+1)=a (3*i))
    (hA : ∀i<N,A (3*i+1)=A (3*i))
    (t : ℝ) (ht : t∈Ioo 0 1) (H : FiniteStateField S) :
    finiteStateGaussianScheduledTerminalTime V a ha A up (3*N) t H=
      (1/2:ℝ)*∑i∈Finset.range N,(if up (3*i+2) then (1:ℝ) else -1)*
        finiteStateCascadeCovarianceResponse V a (fun j=>finiteStateScheduleScale (up j) t • A j)
          (3*i+2) (3*N-(3*i+2)) H (A (3*i+2)) := by
  rw [finiteStateGaussianScheduledTerminal_time_eq_responses V a ha A up _ t ht H,
    sum_range_three_signed]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i<N := Finset.mem_range.mp hi
  rcases hup i hin with ⟨hu0,hu1⟩
  rw [hu0,hu1]
  simp only [Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,hA i hin]
  have he := finiteStateCascadeCovarianceResponse_same_mass V a ha
    (fun j=>finiteStateScheduleScale (up j) t • A j) (3*i) (3*N-(3*i+1))
    (hm i hin) H (A (3*i))
  have hq : 3*N-(3*i+1)+1=3*N-3*i := by omega
  rw [hq] at he
  rw [he]
  ring

end FourPapersCommon
