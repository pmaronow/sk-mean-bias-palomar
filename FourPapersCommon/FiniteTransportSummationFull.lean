module
public import FourPapersCommon.FiniteTransportSummation

@[expose] public section

/-! Full three-way mass sums retain the last original mass drop, with the
extra two same-mass terms proved zero. -/
open scoped BigOperators
namespace FourPapersCommon

theorem sum_threefold_mass_differences_full (a f : ℕ→ℝ) (J : ℕ) :
    (∑p∈Finset.range (3*J),(a ((p+1)/3)-a (p/3))*f (p+1))=
      ∑r∈Finset.range J,(a (r+1)-a r)*f (3*(r+1)) := by
  have he:=sum_threefold_mass_differences a f J
  rw [show 3*J+2=(3*J+1)+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ] at he
  have hz0 : (a ((3*J+1)/3)-a ((3*J)/3))*f (3*J+1)=0 := by
    simp [Nat.mul_comm,Nat.add_div]
  have hz1 : (a ((3*J+1+1)/3)-a ((3*J+1)/3))*f (3*J+1+1)=0 := by
    simp [Nat.mul_comm,Nat.add_div]
  rw [hz0,hz1,add_zero,add_zero] at he
  exact he

end FourPapersCommon
