module
public import QuantitativePaper.FieldSliceJetContinuity

@[expose] public section

/-! Actual retained-variable jets on an open joint domain, with no global
smooth-extension premise. The insertion has norm at most one. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {A E F : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_fieldSlice_eq_on_open (f : A×E → F) (U : Set (A×E)) (hU : IsOpen U)
    (hf : ∀ z ∈ U, ContDiffAt ℝ ∞ f z) (r : ℕ) (a : A) (x : E) (hx : (a,x) ∈ U) :
    iteratedFDeriv ℝ r (fun y => f (a,y)) x =
      (iteratedFDeriv ℝ r f (a,x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ A E) := by
  let L := ContinuousLinearMap.inr ℝ A E
  let V := (fun z : A×E => z+(a,0)) ⁻¹' U
  let g := fun z : A×E => f (z+(a,0))
  have hV : IsOpen V := hU.preimage (by fun_prop)
  have hg : ContDiffOn ℝ ∞ g V := by
    intro z hz
    exact ((hf _ hz).comp z (contDiffAt_id.add contDiffAt_const)).contDiffWithinAt
  have hW : IsOpen (L ⁻¹' V) := hV.preimage L.continuous
  have hxL : L x ∈ V := by simpa [V,L] using hx
  have he := L.iteratedFDerivWithin_comp_right hg hV.uniqueDiffOn hW.uniqueDiffOn hxL
    (i:=r) (by simp)
  rw [iteratedFDerivWithin_of_isOpen r hW hxL,iteratedFDerivWithin_of_isOpen r hV hxL] at he
  simpa only [g,L,Function.comp_def,iteratedFDeriv_comp_add_right,ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk,zero_add,add_zero,add_comm] using he

theorem norm_iteratedFDeriv_fieldSlice_le_joint_on_open (f : A×E → F)
    (U : Set (A×E)) (hU : IsOpen U) (hf : ∀ z ∈ U, ContDiffAt ℝ ∞ f z)
    (r : ℕ) (a : A) (x : E) (hx : (a,x) ∈ U) :
    ‖iteratedFDeriv ℝ r (fun y => f (a,y)) x‖ ≤ ‖iteratedFDeriv ℝ r f (a,x)‖ := by
  rw [iteratedFDeriv_fieldSlice_eq_on_open f U hU hf r a x hx]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hP : (∏ _ : Fin r, ‖ContinuousLinearMap.inr ℝ A E‖) ≤ 1 := by
    simpa only [Finset.prod_const_one] using Finset.prod_le_prod₀
      (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inr_le_one (𝕜:=ℝ) (E:=A) (F:=E))
  exact (mul_le_mul_of_nonneg_left hP (norm_nonneg _)).trans_eq (mul_one _)

end QuantitativePaper
