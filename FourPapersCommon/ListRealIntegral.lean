module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! Finite real list expectations, with integrability of every summand. -/
noncomputable section
open MeasureTheory
namespace FourPapersCommon

theorem integrable_list_map_sum_real {Ω A : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (xs : List A) (f : A→Ω→ℝ) (hf : ∀a,Integrable (f a) P) :
    Integrable (fun ω=>(xs.map (fun a=>f a ω)).sum) P := by
  induction xs with
  | nil => exact integrable_zero _ _ _
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons]
    convert! (hf a).add ih using 1

theorem integral_list_map_sum_real {Ω A : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (xs : List A) (f : A→Ω→ℝ) (hf : ∀a,Integrable (f a) P) :
    (∫ω,(xs.map (fun a=>f a ω)).sum∂P)=(xs.map (fun a=>∫ω,f a ω∂P)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (hf a) (integrable_list_map_sum_real P xs f hf),ih]

theorem integral_list_map_weighted_sum_real {Ω A : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (xs : List A) (w : A→ℝ) (f : A→Ω→ℝ) (F : Ω→ℝ)
    (hf : ∀a,Integrable (fun ω=>F ω*f a ω) P) :
    (∫ω,F ω*(xs.map (fun a=>w a*f a ω)).sum∂P)=
      (xs.map (fun a=>w a*(∫ω,F ω*f a ω∂P))).sum := by
  have he (ω) : F ω*(xs.map (fun a=>w a*f a ω)).sum=
      (xs.map (fun a=>w a*(F ω*f a ω))).sum := by
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    ring
  simp_rw [he]
  rw [integral_list_map_sum_real P xs _ (fun a=>(hf a).const_mul _)]
  simp_rw [integral_const_mul]

end FourPapersCommon
