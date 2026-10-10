module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

@[expose] public section

/-! Genuine conditional expectation linearity for a finite quadratic
observable expansion. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace FourPapersCommon
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

theorem condExp_double_sum_coeff (P : Measure Ω) (m : MeasurableSpace Ω)
    (F : ι→ι→Ω→ℝ) (w : ι→ℝ) (hF : ∀i j,Integrable (F i j) P) :
    P[(fun x=>∑i,∑j,(w i*w j)*F i j x)|m]=ᵐ[P]
      fun x=>∑i,∑j,(w i*w j)*P[F i j|m] x := by
  have hi (i j : ι) : Integrable (fun x=>(w i*w j)*F i j x) P:=(hF i j).const_mul _
  have hinner (i : ι) : P[(fun x=>∑j,(w i*w j)*F i j x)|m]=ᵐ[P]
      fun x=>∑j,(w i*w j)*P[F i j|m] x := by
    have hs:=condExp_finsetSum (μ:=P) (s:=Finset.univ) (fun j _=>hi i j) m
    have he : (∑j : ι,fun x=>(w i*w j)*F i j x)=
        (fun x=>∑j,(w i*w j)*F i j x) := by funext x;simp only [Finset.sum_apply]
    rw [he] at hs
    have hm : ∀j : ι,P[(fun x=>(w i*w j)*F i j x)|m]=ᵐ[P]
        fun x=>(w i*w j)*P[F i j|m] x := by
      intro j
      simpa only [Pi.smul_def,smul_eq_mul] using condExp_smul (μ:=P) (w i*w j) (F i j) m
    filter_upwards [hs,ae_all_iff.mpr hm] with x hx hall
    simp only [Finset.sum_apply] at hx
    exact hx.trans (Finset.sum_congr rfl fun j _=>hall j)
  have hiSum (i : ι) : Integrable (fun x=>∑j,(w i*w j)*F i j x) P:=
    integrable_finsetSum Finset.univ fun j _=>hi i j
  have hs:=condExp_finsetSum (μ:=P) (s:=Finset.univ) (fun i _=>hiSum i) m
  have he : (∑i : ι,fun x=>∑j,(w i*w j)*F i j x)=
      (fun x=>∑i,∑j,(w i*w j)*F i j x) := by funext x;simp only [Finset.sum_apply]
  rw [he] at hs
  filter_upwards [hs,ae_all_iff.mpr hinner] with x hx hall
  simp only [Finset.sum_apply] at hx
  exact hx.trans (Finset.sum_congr rfl fun i _=>hall i)

end FourPapersCommon
