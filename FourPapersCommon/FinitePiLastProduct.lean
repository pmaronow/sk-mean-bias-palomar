module
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! Split a genuine finite product law at one coordinate while keeping
an arbitrary observable of all other coordinates together. -/
noncomputable section
open MeasureTheory
namespace FourPapersCommon
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

theorem integral_pi_coordinate_product {C : ℕ} {E : Fin (C+1) → Type*}
    [∀i,MeasurableSpace (E i)] (μ : ∀i,Measure (E i)) [∀i,SigmaFinite (μ i)]
    (i : Fin (C+1)) (F : ((j : Fin C) → E (i.succAbove j)) → ℝ) (G : E i → ℝ) :
    (∫σ, F (fun j => σ (i.succAbove j))*G (σ i) ∂Measure.pi μ) =
      (∫τ, F τ ∂Measure.pi (fun j : Fin C => μ (i.succAbove j)))*
        (∫z, G z ∂μ i) := by
  have hp := measurePreserving_piFinSuccAbove μ i
  calc
    _ = ∫z : E i × ((j : Fin C) → E (i.succAbove j)),
        G z.1*F z.2 ∂(μ i).prod (Measure.pi (fun j : Fin C => μ (i.succAbove j))) := by
      rw [←hp.symm.integral_comp']
      congr 1
      funext z
      simp only [Function.comp_apply,MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv,Equiv.coe_fn_mk,Fin.insertNth_apply_same,
        Fin.insertNth_apply_succAbove]
      ring
    _ = _ := by
      rw [integral_prod_mul (μ := μ i)
        (ν := Measure.pi (fun j : Fin C => μ (i.succAbove j))) G F]
      ring

end FourPapersCommon
