module
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Finite Gram contraction without a covariance premise hidden in a
definition. The coordinate sum is expanded into all actual mark pairs. -/
noncomputable section
open scoped BigOperators
namespace FourPapersCommon
variable {A I : Type} [Fintype I]

theorem finset_sum_list_map_comm (cs : List A) (f : I→A→ℝ) :
    (∑i,(cs.map (f i)).sum)=(cs.map (fun c=>∑i,f i c)).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

theorem list_sum_product_pairs (cs : List A) (f g : A→ℝ) :
    (cs.map f).sum*(cs.map g).sum=
      (cs.map (fun c=>(cs.map (fun d=>f c*g d)).sum)).sum := by
  simp_rw [List.sum_map_mul_left]
  exact (List.sum_map_mul_right cs f (cs.map g).sum).symm

theorem finite_weighted_gram_contraction (cs : List (ℝ×A)) (p : A→I→ℝ) :
    (∑i,((cs.map (fun c=>c.1*p c.2 i)).sum)^2)=
      (cs.map (fun c=>(cs.map (fun d=>
        c.1*d.1*(∑i,p c.2 i*p d.2 i))).sum)).sum := by
  have he (i : I) : ((cs.map (fun c=>c.1*p c.2 i)).sum)^2=
      (cs.map (fun c=>(cs.map (fun d=>(c.1*p c.2 i)*(d.1*p d.2 i))).sum)).sum := by
    rw [pow_two,list_sum_product_pairs]
  simp_rw [he]
  rw [finset_sum_list_map_comm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c _
  rw [finset_sum_list_map_comm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end FourPapersCommon
