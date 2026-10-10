module
public import FourPapersCommon.FiniteStateCovarianceScheduleTrace

@[expose] public section

/-! Cancellation of opposite covariance directions at two consecutive
same-mass Gaussian levels. These are identities of actual normalized
cascade responses, rather than assumed interpolation estimates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
set_option maxHeartbeats 1200000
variable {S I : Type*} [Fintype S] [Fintype I] [DecidableEq I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

theorem finiteStateCascadeCovarianceResponse_same_mass
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j q : ℕ) (hm : a (j+1)=a j) (H : FiniteStateField S)
    (A : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) :
    finiteStateCascadeCovarianceResponse V a L (j+1) q H A =
      finiteStateCascadeCovarianceResponse V a L j (q+1) H A := by
  rw [finiteStateCascadeCovarianceResponse_eq_split_moments V a ha,
    finiteStateCascadeCovarianceResponse_eq_split_moments V a ha]
  rw [show j+1+q=j+(q+1) by omega,Finset.sum_range_succ,hm,sub_self,
    zero_mul,add_zero]

private theorem sum_range_three {E : Type*} [AddCommMonoid E] (f : ℕ → E) (n : ℕ) :
    (∑ j ∈ Finset.range (3*n),f j)=
      ∑ i ∈ Finset.range n,(f (3*i)+f (3*i+1)+f (3*i+2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3*(n+1)=((3*n+1)+1)+1 by omega]
    rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,ih,
      Finset.sum_range_succ]
    ac_rfl

/-- In a three-level covariance schedule, the decreasing base direction and
its increasing copy cancel exactly. Only the active increasing direction
remains, including zero directions and zero masses. -/
theorem finiteStateGaussianScheduledTerminal_time_threefold
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (A : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (up : ℕ→Bool) (N : ℕ)
    (hup : ∀i<N,up (3*i)=false ∧ up (3*i+1)=true ∧ up (3*i+2)=true)
    (hm : ∀i<N,a (3*i+1)=a (3*i))
    (hA : ∀i<N,A (3*i+1)=A (3*i))
    (t : ℝ) (ht : t∈Ioo 0 1) (H : FiniteStateField S) :
    finiteStateGaussianScheduledTerminalTime V a ha A up (3*N) t H =
      (1/2 : ℝ)*∑i∈Finset.range N,
        finiteStateCascadeCovarianceResponse V a (fun j=>finiteStateScheduleScale (up j) t • A j)
          (3*i+2) (3*N-(3*i+2)) H (A (3*i+2)) := by
  rw [finiteStateGaussianScheduledTerminal_time_eq_responses V a ha A up _ t ht H,
    sum_range_three]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i<N := Finset.mem_range.mp hi
  rcases hup i hin with ⟨hu0,hu1,hu2⟩
  rw [hu0,hu1,hu2]
  simp only [Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,hA i hin]
  have he:=finiteStateCascadeCovarianceResponse_same_mass V a ha
    (fun j=>finiteStateScheduleScale (up j) t • A j) (3*i) (3*N-(3*i+1))
    (hm i hin) H (A (3*i))
  have hq : 3*N-(3*i+1)+1=3*N-3*i := by omega
  rw [hq] at he
  rw [he]
  ring

end FourPapersCommon
