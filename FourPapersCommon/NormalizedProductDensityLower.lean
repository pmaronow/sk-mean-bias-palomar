module
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! An actual conditional raw-density lower bound transfers through
independent background coordinates by genuine Fubini and normalization. -/
noncomputable section
open MeasureTheory Set
namespace FourPapersCommon

theorem lower_bound_normalized_product_density {E F : Type*}
    [MeasurableSpace E] [MeasurableSpace F]
    (P : Measure E) (Q : Measure F) [SFinite P] [SFinite Q]
    (V H : E×F→ℝ) (c B : ℝ)
    (hI : Integrable (fun z=>Real.exp (V z)) (P.prod Q))
    (hH : AEStronglyMeasurable H (P.prod Q)) (hHb : ∀z,|H z|≤B)
    (hZ : 0<∫z,Real.exp (V z)∂P.prod Q)
    (hpoint : ∀b,c*(∫g,Real.exp (V (g,b))∂P)≤
      ∫g,Real.exp (V (g,b))*H (g,b)∂P) :
    c≤(∫z,Real.exp (V z)*H z∂P.prod Q)/(∫z,Real.exp (V z)∂P.prod Q) := by
  have hIH : Integrable (fun z=>Real.exp (V z)*H z) (P.prod Q) :=
    hI.mul_bdd hH (.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hHb z)
  have hh := integral_mono (hI.integral_prod_right.const_mul c) hIH.integral_prod_right hpoint
  rw [integral_const_mul,←integral_prod_symm _ hI,←integral_prod_symm _ hIH] at hh
  exact (le_div_iff₀ hZ).mpr hh

end FourPapersCommon
