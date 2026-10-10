module
public import QuantitativePaper.SmoothGaussianStep
public import QuantitativePaper.VectorRecursionIntegrability

@[expose] public section

/-! Translation-invariant Gaussian averaging preserves the actual terminal
Lipschitz bound. This applies to arbitrary retained energy parameters. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem gaussianShiftColeHopf_eq_unitVectorStep (A : Field n→L[ℝ] E) (m : ℝ)
    (f : E→ℝ) (p : E) :
    gaussianShiftColeHopf A m f p=
      vectorColeHopfStep 1 m (fun z=>f (p+A z)) 0 := by
  unfold gaussianShiftColeHopf gaussianShiftAverage gaussianShiftPartition
    vectorColeHopfStep vectorStepPartition
  simp only [fieldShift,Real.sqrt_one,one_smul,zero_add]

theorem lipschitzWith_gaussianShiftColeHopf (A : Field n→L[ℝ] E) (m : ℝ)
    (hm : 0 ≤ m) (f : E→ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) :
    LipschitzWith L (gaussianShiftColeHopf A m f) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [Real.dist_eq,gaussianShiftColeHopf_eq_unitVectorStep,gaussianShiftColeHopf_eq_unitVectorStep]
  have hshift (r : E) : LipschitzWith ‖A‖₊ (fun z => r+A z) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [dist_add_left] using A.lipschitzWith.dist_le_mul z w
  apply abs_vectorColeHopfStep_sub_le _ _ (L*‖A‖₊)
    (hf.comp (hshift p)) (hf.comp (hshift q))
    1 m ((L:ℝ)*dist p q) hm
  · intro z
    have H:=hf.dist_le_mul (p+A z) (q+A z)
    simpa only [Real.dist_eq,dist_add_right,Function.comp_def] using H

end QuantitativePaper
