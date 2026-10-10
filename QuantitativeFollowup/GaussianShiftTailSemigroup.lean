module
public import QuantitativeFollowup.GaussianShiftSemigroup
public import QuantitativePaper.VectorTailRefinement

@[expose] public section

/-! True restarted Gaussian cascades with arbitrary fixed covariance map.
Coarse-to-fine equality includes the cell containing the restart time. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
open scoped NNReal ContDiff
namespace QuantitativeFollowup
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

def gaussianUniformTailCascade (N : ℕ) (q : ℝ) (A : Field n →L[ℝ] E)
    (a : ℝ→ℝ) (f : E→ℝ) : ℕ→E→ℝ
  | 0 => f
  | j+1 => gaussianShiftColeHopf
      (Real.sqrt (max q ((N-j : ℕ)/(N : ℝ))-max q ((N-1-j : ℕ)/(N : ℝ))) • A)
      (a ((N-1-j : ℕ)/(N : ℝ))) (gaussianUniformTailCascade N q A a f j)

theorem gaussianUniformTailCascade_comp_shift (N : ℕ) (q : ℝ) (A : Field n→L[ℝ]E)
    (a : ℝ→ℝ) (f : E→ℝ) (j : ℕ) (x : E) :
    (fun y => gaussianUniformTailCascade N q A a f j (x+A y))=
      vectorUniformTailCascade N 1 q a (fun y => f (x+A y)) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext y
    rw [gaussianUniformTailCascade,gaussianShiftColeHopf_smul_eq_vectorStep,ih,vectorUniformTailCascade]
    simp only [one_mul]

theorem gaussianUniformTailCascade_coarse_double (μ : Paper.ParisiMeasure) (N : ℕ)
    (q : ℝ) (A : Field n→L[ℝ]E) (f : E→ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) :
    gaussianUniformTailCascade (2*(N+1)) q A (Paper.parisiCDF (Paper.parisiGridMeasure μ N)) f (2*(N+1))=
      gaussianUniformTailCascade (N+1) q A (Paper.parisiCDF μ) f (N+1) := by
  funext x
  have h1 := congrFun (gaussianUniformTailCascade_comp_shift (2*(N+1)) q A
    (Paper.parisiCDF (Paper.parisiGridMeasure μ N)) f (2*(N+1)) x) 0
  have h2 := congrFun (gaussianUniformTailCascade_comp_shift (N+1) q A (Paper.parisiCDF μ) f (N+1) x) 0
  simp only [map_zero,add_zero] at h1 h2
  rw [h1,h2]
  exact congrFun (vectorUniformTailCascade_coarse_double μ N 1 q zero_le_one
    (fun y => f (x+A y)) (L*‖A‖₊) (lipschitz_gaussianShift_input f L hf A x)) 0

end QuantitativeFollowup
