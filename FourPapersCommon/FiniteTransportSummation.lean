module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

@[expose] public section

/-! Exact finite summation identities for transported covariance cells.
No differentiability or response representation is assumed here. -/
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1600000

private theorem transport_sum_range_three {E : Type*} [AddCommMonoid E]
    (f : ℕ→E) (n : ℕ) :
    (∑j∈Finset.range (3*n),f j)=∑i∈Finset.range n,(f (3*i)+f (3*i+1)+f (3*i+2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3*(n+1)=((3*n+1)+1)+1 by omega]
    rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,ih,Finset.sum_range_succ]
    ac_rfl

theorem sum_threefold_mass_differences (a f : ℕ→ℝ) (i : ℕ) :
    (∑p∈Finset.range (3*i+2),(a ((p+1)/3)-a (p/3))*f (p+1))=
      ∑r∈Finset.range i,(a (r+1)-a r)*f (3*(r+1)) := by
  let g:=fun p=>(a ((p+1)/3)-a (p/3))*f (p+1)
  have hz0 (r : ℕ) : g (3*r)=0 := by simp [g,Nat.mul_comm,Nat.add_div]
  have hz1 (r : ℕ) : g (3*r+1)=0 := by simp [g,Nat.mul_comm,Nat.add_div]
  change (∑p∈Finset.range (3*i+2),g p)=_
  rw [show 3*i+2=(3*i+1)+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,
    hz1,hz0,add_zero,add_zero,transport_sum_range_three]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hz0,hz1,zero_add,zero_add]
  dsimp only [g]
  rw [show (3*r+2+1)/3=r+1 by omega,show (3*r+2)/3=r by omega,
    show 3*r+2+1=3*(r+1) by omega]

theorem sum_transport_cell_response (B A : ℕ→ℝ) (J : ℕ) :
    (∑i∈Finset.range J,(B i-B (i+1))*(1+∑r∈Finset.range i,A r))=
      B 0-B J+∑r∈Finset.range J,A r*(B (r+1)-B J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ,ih,Finset.sum_range_succ]
    simp only [sub_self,mul_zero,add_zero]
    have he : (∑r∈Finset.range J,A r*(B (r+1)-B (J+1)))=
        (∑r∈Finset.range J,A r*(B (r+1)-B J))+
          (B J-B (J+1))*(∑r∈Finset.range J,A r) := by
      rw [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [he]
    ring

theorem sum_transport_cell_response_of_terminal_zero (B A : ℕ→ℝ) (hB : B 0=0) (J : ℕ) :
    (∑i∈Finset.range J,(B i-B (i+1))*(1+∑r∈Finset.range i,A r))=
      -(B J*(1+∑r∈Finset.range J,A r)-∑r∈Finset.range J,A r*B (r+1)) := by
  rw [sum_transport_cell_response,hB]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,←Finset.sum_mul]
  ring

end FourPapersCommon
