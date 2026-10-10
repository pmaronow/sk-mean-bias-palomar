module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterSchemeStieltjes

@[expose] public section

/-! Literal free integrals are finite signed sums. Their real linearity
therefore holds for every finite-valued test, including all kernel and
conditional-moment sections used in the independent-endpoint grouping. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option autoImplicit false

theorem integral_cavityFiniteFree_add (s : RSBScheme k)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (F G : Paper.Overlap→ℝ) :
    (∫r,F r+G r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)=
      (∫r,F r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)+
        ∫r,G r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  rw [←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq (fun r=>F r+G r),
    ←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq F,
    ←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq G]
  simp only [mul_add,Finset.sum_add_distrib]

theorem integral_cavityFiniteFree_sub (s : RSBScheme k)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (F G : Paper.Overlap→ℝ) :
    (∫r,F r-G r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)=
      (∫r,F r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)-
        ∫r,G r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  rw [←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq (fun r=>F r-G r),
    ←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq F,
    ←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq G]
  simp only [mul_sub,Finset.sum_sub_distrib]

theorem integral_cavityFiniteFree_finset_sum {I : Type*} (t : Finset I)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (F : I→Paper.Overlap→ℝ) :
    (∫r,∑i∈t,F i r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)=
      ∑i∈t,∫r,F i r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  rw [←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq (fun r=>∑i∈t,F i r)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq (F i)

end QuantitativeFollowup
