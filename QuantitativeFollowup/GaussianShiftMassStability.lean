module
public import QuantitativePaper.VectorMassBounds
public import QuantitativePaper.SmoothGaussianStep

@[expose] public section

/-! Genuine mass and input stability of an arbitrary finite-dimensional
Gaussian shift. The covariance operator may be anisotropic or singular. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
open scoped NNReal ContDiff
namespace QuantitativeFollowup
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
set_option maxHeartbeats 1400000

theorem lipschitz_gaussianShift_input (f : E→ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (A : Field n→L[ℝ]E) (x : E) :
    LipschitzWith (L*‖A‖₊) (fun z => f (x+A z)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hh := hf.norm_sub_le (x+A z) (x+A w)
  simp only [add_sub_add_left_eq_sub,←map_sub] at hh
  rw [Real.dist_eq,dist_eq_norm]
  exact hh.trans (by simpa only [NNReal.coe_mul,coe_nnnorm,mul_assoc] using
    mul_le_mul_of_nonneg_left (A.le_opNorm (z-w)) L.coe_nonneg)

theorem gaussianShiftColeHopf_eq_unit_vectorStep (A : Field n→L[ℝ]E) (m : ℝ)
    (f : E→ℝ) (x : E) :
    gaussianShiftColeHopf A m f x=vectorColeHopfStep 1 m (fun z => f (x+A z)) 0 := by
  simp only [gaussianShiftColeHopf,gaussianShiftAverage,gaussianShiftPartition,
    vectorColeHopfStep,vectorStepPartition,fieldShift,Real.sqrt_one,one_smul,zero_add]

theorem gaussianShiftColeHopf_mass_abs_sub_le (f : E→ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (hs : ContDiff ℝ 1 f) (A : Field n→L[ℝ]E)
    (x : E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |gaussianShiftColeHopf A a f x-gaussianShiftColeHopf A b f x| ≤
      ((L : ℝ)*‖A‖)^2*|a-b| := by
  rw [gaussianShiftColeHopf_eq_unit_vectorStep,gaussianShiftColeHopf_eq_unit_vectorStep]
  have hh := vectorColeHopfStep_mass_abs_sub_le (fun z => f (x+A z)) (L*‖A‖₊)
    (lipschitz_gaussianShift_input f L hf A x) (hs.comp (contDiff_const.add A.contDiff))
    1 0 b a hb ha
  simpa only [NNReal.coe_mul,coe_nnnorm,Real.sqrt_one,mul_one] using hh

theorem gaussianShiftColeHopf_input_abs_sub_le (f g : E→ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (hg : LipschitzWith L g)
    (A : Field n→L[ℝ]E) (a : ℝ) (ha : 0 ≤ a) (C : ℝ)
    (hb : ∀ x,|f x-g x| ≤ C) (x : E) :
    |gaussianShiftColeHopf A a f x-gaussianShiftColeHopf A a g x| ≤ C := by
  rw [gaussianShiftColeHopf_eq_unit_vectorStep,gaussianShiftColeHopf_eq_unit_vectorStep]
  exact abs_vectorColeHopfStep_sub_le (fun z => f (x+A z)) (fun z => g (x+A z))
    (L*‖A‖₊) (lipschitz_gaussianShift_input f L hf A x)
    (lipschitz_gaussianShift_input g L hg A x) 1 a C ha (fun z => hb _) 0

end QuantitativeFollowup
