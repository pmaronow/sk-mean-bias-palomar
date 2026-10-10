module
public import QuantitativeFollowup.ScalarFiniteScoreContraction

@[expose] public section

/-! Exact finite expansions of the terminal-spin and potential scores.
The Gaussian quadratic score is expanded before any expectation or future
conditioning is performed. -/
noncomputable section
open scoped BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000

def finiteCoordinateScore {ι α : Type*} [Fintype α] [DecidableEq ι]
    (terminal : ι) (ε : ℝ) (node : α→ι) (a : α→ℝ) (j : ι) : ℝ :=
  (if terminal=j then ε else 0)-∑i,if node i=j then a i else 0

theorem finiteCoordinateScore_linear {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] (terminal : ι) (ε : ℝ) (node : α→ι) (a : α→ℝ) (f : ι→ℝ) :
    (∑j,f j*finiteCoordinateScore terminal ε node a j)=
      ε*f terminal-∑i,a i*f (node i) := by
  unfold finiteCoordinateScore
  simp_rw [mul_sub,mul_ite,mul_zero,Finset.mul_sum,Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _=>by
      simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      ring

theorem finiteCoordinateScore_quadratic {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] (terminal : ι) (ε : ℝ) (node : α→ι) (a : α→ℝ)
    (K : ι→ι→ℝ) (hK : ∀i j,K i j=K j i) :
    (∑i,∑j,K i j*finiteCoordinateScore terminal ε node a i*
      finiteCoordinateScore terminal ε node a j)=
      ε^2*K terminal terminal-2*ε*(∑i,a i*K (node i) terminal)+
        ∑i,∑j,a i*a j*K (node i) (node j) := by
  let b := finiteCoordinateScore terminal ε node a
  have hi (i : ι) : (∑j,K i j*b i*b j)=
      b i*(ε*K i terminal-∑j,a j*K i (node j)) := by
    rw [show (∑j,K i j*b i*b j)=b i*(∑j,K i j*b j) from by
      rw [Finset.mul_sum];exact Finset.sum_congr rfl fun j _=>by ring]
    rw [finiteCoordinateScore_linear]
  change (∑i,∑j,K i j*b i*b j)=_
  simp_rw [hi,mul_sub,Finset.sum_sub_distrib]
  have hfirst : (∑i,b i*(ε*K i terminal))=
      ε*(ε*K terminal terminal-∑i,a i*K (node i) terminal) := by
    rw [show (∑i,b i*(ε*K i terminal))=ε*(∑i,K i terminal*b i) from by
      rw [Finset.mul_sum];exact Finset.sum_congr rfl fun i _=>by ring]
    rw [finiteCoordinateScore_linear]
  have hsecond : (∑i,b i*(∑j,a j*K i (node j)))=
      ε*(∑j,a j*K (node j) terminal)-(∑i,∑j,a i*a j*K (node i) (node j)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hj (j : α) : (∑i,b i*(a j*K i (node j)))=
        a j*(ε*K terminal (node j)-∑i,a i*K (node i) (node j)) := by
      rw [show (∑i,b i*(a j*K i (node j)))=a j*(∑i,K i (node j)*b i) from by
        rw [Finset.mul_sum];exact Finset.sum_congr rfl fun i _=>by ring]
      rw [finiteCoordinateScore_linear]
    simp_rw [hj,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _=>by rw [hK];ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>by ring
  rw [hfirst,hsecond]
  ring

end QuantitativeFollowup
