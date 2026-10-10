module
public import QuantitativeFollowup.GaussianShiftMassStability
public import QuantitativePaper.VectorDyadicRefinement

@[expose] public section

/-! Honest composition and common dyadic refinement for Gaussian steps
with an arbitrary fixed shift operator. This includes anisotropic fields. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
open scoped NNReal ContDiff
namespace QuantitativeFollowup
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
set_option maxHeartbeats 1400000

theorem gaussianShiftColeHopf_smul_eq_vectorStep (A : Field n→L[ℝ]E) (v m : ℝ)
    (f : E→ℝ) (x : E) (y : Field n) :
    gaussianShiftColeHopf (Real.sqrt v • A) m f (x+A y)=
      vectorColeHopfStep v m (fun z => f (x+A z)) y := by
  unfold gaussianShiftColeHopf gaussianShiftAverage gaussianShiftPartition
    vectorColeHopfStep vectorStepPartition fieldShift
  simp only [ContinuousLinearMap.smul_apply,map_add,map_smul,add_assoc]

theorem gaussianShiftColeHopf_semigroup (f : E→ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (A : Field n→L[ℝ]E) (m : ℝ) (hm : 0 ≤ m) (v w : ℝ)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (x : E) :
    gaussianShiftColeHopf (Real.sqrt v • A) m (gaussianShiftColeHopf (Real.sqrt w • A) m f) x=
      gaussianShiftColeHopf (Real.sqrt (v+w) • A) m f x := by
  have he : (fun y => gaussianShiftColeHopf (Real.sqrt w • A) m f (x+A y))=
      vectorColeHopfStep w m (fun z => f (x+A z)) :=
    funext fun y => gaussianShiftColeHopf_smul_eq_vectorStep A w m f x y
  have hx : x=x+A (0 : Field n) := by simp
  conv_lhs => arg 4;rw [hx]
  rw [gaussianShiftColeHopf_smul_eq_vectorStep,he]
  rw [vectorColeHopfStep_semigroup _ (L*‖A‖₊) (lipschitz_gaussianShift_input f L hf A x) m hm v w hv hw]
  simpa only [map_zero,add_zero] using (gaussianShiftColeHopf_smul_eq_vectorStep A (v+w) m f x 0).symm

def gaussianUniformGridCascade (N : ℕ) (A : Field n→L[ℝ]E) (a : ℝ→ℝ) (f : E→ℝ) : ℕ→E→ℝ
  | 0 => f
  | j+1 => gaussianShiftColeHopf (Real.sqrt (1/(N : ℝ)) • A) (a ((N-1-j : ℕ)/(N : ℝ)))
      (gaussianUniformGridCascade N A a f j)

theorem gaussianUniformGridCascade_comp_shift (N : ℕ) (A : Field n→L[ℝ]E)
    (a : ℝ→ℝ) (f : E→ℝ) (j : ℕ) (x : E) :
    (fun y => gaussianUniformGridCascade N A a f j (x+A y))=
      vectorUniformGridCascade N 1 a (fun y => f (x+A y)) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext y
    rw [gaussianUniformGridCascade,gaussianShiftColeHopf_smul_eq_vectorStep,ih,vectorUniformGridCascade]

theorem gaussianUniformGridCascade_coarse_double (μ : Paper.ParisiMeasure) (N : ℕ)
    (A : Field n→L[ℝ]E) (f : E→ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) :
    gaussianUniformGridCascade (2*(N+1)) A (Paper.parisiCDF (Paper.parisiGridMeasure μ N)) f (2*(N+1))=
      gaussianUniformGridCascade (N+1) A (Paper.parisiCDF μ) f (N+1) := by
  funext x
  have h1 := congrFun (gaussianUniformGridCascade_comp_shift (2*(N+1)) A
    (Paper.parisiCDF (Paper.parisiGridMeasure μ N)) f (2*(N+1)) x) 0
  have h2 := congrFun (gaussianUniformGridCascade_comp_shift (N+1) A (Paper.parisiCDF μ) f (N+1) x) 0
  simp only [map_zero,add_zero] at h1 h2
  rw [h1,h2]
  exact congrFun (vectorUniformGridCascade_coarse_double μ N 1 zero_le_one
    (fun y => f (x+A y)) (L*‖A‖₊) (lipschitz_gaussianShift_input f L hf A x)) 0

end QuantitativeFollowup
