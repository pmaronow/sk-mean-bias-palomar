module
public import QuantitativePaper.VectorPartialJets

@[expose] public section

/-! Actual full-order jet bounds of a fixed-parameter field slice. The
parameter insertion has operator norm at most one for the product norm. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_fieldSlice_le (f : A×E → F) {N j : ℕ}
    (hf : ContDiff ℝ N f) (hj : j≤N) (a : A) (x : E)
    (C : ℝ) (hC : 0≤C) (hB : ∀ z,‖iteratedFDeriv ℝ j f z‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun y=>f (a,y)) x‖ ≤ C := by
  let L : E→L[ℝ] A×E := ContinuousLinearMap.inr ℝ A E
  have hL : ‖L‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    simp [L,Prod.norm_def]
  let G : A×E → F := fun z=>f (z+(a,0))
  have hG : ContDiff ℝ N G := hf.comp (contDiff_id.add contDiff_const)
  have he : (fun y=>f (a,y))=G ∘ L := by
    funext y
    simp [G,L,Function.comp_def]
  rw [he,L.iteratedFDeriv_comp_right hG x (by exact_mod_cast hj)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [iteratedFDeriv_comp_add_right]
  have hh := mul_le_mul_of_nonneg_right (hB (L x+(a,0))) (pow_nonneg (norm_nonneg L) j)
  apply hh.trans
  have hp : ‖L‖^j≤1 := by simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg L) hL j
  exact (mul_le_mul_of_nonneg_left hp hC).trans_eq (mul_one _)

theorem lipschitzWith_fieldSlice {f : A×E → F} {L : ℝ≥0}
    (hf : LipschitzWith L f) (a : A) : LipschitzWith L (fun y=>f (a,y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0≤dist x y)] using hf.dist_le_mul (a,x) (a,y)

end QuantitativePaper
