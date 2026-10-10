module
public import FourPapersCommon.FiniteWeightedGram
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact expansion of a signed finite Gram matrix into original-original,
original-charge and charge-charge pairs. -/
noncomputable section
namespace FourPapersCommon
variable {A B : Type}

theorem list_sum_map_neg_real (xs : List A) (f : A→ℝ) :
    (xs.map (fun x=>-f x)).sum=-(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih];ring

theorem list_sum_map_sub_real (xs : List A) (f g : A→ℝ) :
    (xs.map (fun x=>f x-g x)).sum=(xs.map f).sum-(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih];ring

theorem list_sum_map_div_real (xs : List A) (f : A→ℝ) (d : ℝ) :
    (xs.map (fun x=>f x/d)).sum=(xs.map f).sum/d := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih];ring

open scoped BigOperators in
theorem finite_weighted_defect_contraction {I : Type} [Fintype I]
    (cs : List (ℝ×A)) (p : A→I→ℝ) (e : A→ℝ) (K : A→A→ℝ) (d : ℝ) :
    (∑i,((cs.map (fun c=>c.1*p c.2 i)).sum)^2)/d-
      (cs.map (fun c=>(cs.map (fun z=>c.1*e c.2*(z.1*e z.2)*K c.2 z.2)).sum)).sum=
        (cs.map (fun c=>(cs.map (fun z=>c.1*z.1*
          ((∑i,p c.2 i*p z.2 i)/d-K c.2 z.2*e c.2*e z.2))).sum)).sum := by
  rw [finite_weighted_gram_contraction]
  have he (x y t s u v : ℝ) : x*y*(t/d-s*u*v)=x*y*t/d-x*u*(y*v)*s := by ring
  simp_rw [he,list_sum_map_sub_real,list_sum_map_div_real]

theorem list_double_sum_comm_real (xs : List A) (ys : List B) (f : A→B→ℝ) :
    (xs.map (fun x=>(ys.map (f x)).sum)).sum=
      (ys.map (fun y=>(xs.map (fun x=>f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,ih,List.sum_map_add]

theorem list_signed_gram_expansion (xs : List A) (ys : List B) (w : B→ℝ)
    (K : Sum A B→Sum A B→ℝ) (hK : ∀x y,K x y=K y x) :
    let cs:=xs.map (fun x=>((1:ℝ),Sum.inl x))++ys.map (fun y=>(-w y,Sum.inr y))
    (cs.map (fun c=>(cs.map (fun d=>c.1*d.1*K c.2 d.2)).sum)).sum=
      (xs.map (fun x=>(xs.map (fun z=>K (.inl x) (.inl z))).sum)).sum-
        2*(xs.map (fun x=>(ys.map (fun y=>w y*K (.inl x) (.inr y))).sum)).sum+
        (ys.map (fun y=>(ys.map (fun z=>w y*w z*K (.inr y) (.inr z))).sum)).sum := by
  dsimp only
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,
    one_mul,mul_one,neg_mul,mul_neg,neg_mul_neg]
  simp_rw [list_sum_map_neg_real,List.sum_map_add]
  simp_rw [list_sum_map_neg_real,neg_neg]
  have hc : (ys.map (fun y=>(xs.map (fun x=>w y*K (.inr y) (.inl x))).sum)).sum=
      (xs.map (fun x=>(ys.map (fun y=>w y*K (.inl x) (.inr y))).sum)).sum := by
    rw [list_double_sum_comm_real]
    apply congrArg List.sum
    apply List.map_congr_left
    intro x _
    apply congrArg List.sum
    apply List.map_congr_left
    intro y _
    rw [hK]
  rw [hc]
  ring

end FourPapersCommon
