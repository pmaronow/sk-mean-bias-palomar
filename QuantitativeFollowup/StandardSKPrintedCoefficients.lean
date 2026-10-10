module
public import QuantitativeFollowup.StandardSKAnisotropicModel

@[expose] public section

/-! The exact coefficients printed in the two Gaussian models of Section 2. -/
noncomputable section
namespace QuantitativeFollowup
open QuantitativePaper
variable {n : ℕ}

theorem standardSKPrintedCoupling_offDiagonal (hn : 0<n) (β t : ℝ) (hβ : β≠0)
    (ht : t<1) (ht0 : 0≤t) (e : AnisotropicCouplingIndex n) (he : e.1.1≠e.1.2) :
    (standardSKAnisotropicModel n β t hβ ht).coupling e=β*Real.sqrt (t/(n:ℝ)) := by
  simp only [standardSKAnisotropicModel,he,ite_false]
  rw [Real.sqrt_div ht0]
  ring

theorem standardSKPrintedCoupling_diagonal (hn : 0<n) (β t : ℝ) (hβ : β≠0)
    (ht : t<1) (ht0 : 0≤t) (e : AnisotropicCouplingIndex n) (he : e.1.1=e.1.2) :
    (standardSKAnisotropicModel n β t hβ ht).coupling e=β*Real.sqrt (t/(2*(n:ℝ))) := by
  have hn0 : (0:ℝ)<n:=by exact_mod_cast hn
  have hn2 : (n:ℝ)≠0:=hn0.ne'
  have hs2 : Real.sqrt (2:ℝ)≠0:=(Real.sqrt_pos.2 (by norm_num)).ne'
  have hsn : Real.sqrt (n:ℝ)≠0:=(Real.sqrt_pos.2 hn0).ne'
  simp only [standardSKAnisotropicModel,he,ite_true]
  rw [Real.sqrt_div (by norm_num : (0:ℝ)≤2),Real.sqrt_div ht0,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

theorem standardSKPrintedVariance (β t : ℝ) (hβ : β≠0) (ht : t<1) (i : Fin n) :
    (standardSKAnisotropicModel n β t hβ ht).variance i=β^2*(1-t) := by
  simp only [standardSKAnisotropicModel]
  ring

end QuantitativeFollowup
