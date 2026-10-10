module
public import FourPapersCommon.VectorDriftTaylor

@[expose] public section

/-! Polynomial norm bounds for the actual Taylor remainder when the drift
increment has a deterministic bound. -/
noncomputable section
open scoped ContDiff
namespace FourPapersCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_add_cube_le (w v : E) :
    ‖w+v‖^3 ≤ 4*(‖w‖^3+‖v‖^3) := by
  have hpow : ‖w+v‖^3 ≤ (‖w‖+‖v‖)^3 := by
    gcongr
    exact norm_add_le w v
  have hpos : 0 ≤ (‖w‖+‖v‖)*(‖w‖-‖v‖)^2 :=
    mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (sq_nonneg _)
  nlinarith

theorem vector_bounded_drift_taylor_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {K₂ K₃ M : ℝ} (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃) (hM : 0 ≤ M)
    (h₂ : ∀ x,‖iteratedFDeriv ℝ 2 f x‖ ≤ K₂)
    (h₃ : ∀ x,‖iteratedFDeriv ℝ 3 f x‖ ≤ K₃)
    (x w v : E) (hv : ‖v‖ ≤ M) :
    |f (x+w+v)-vectorNoiseDriftTaylorPolynomial f x w v| ≤
      2*K₃*‖w‖^3+2*K₃*M^3+K₂*‖w‖*M+K₂/2*M^2 := by
  have hc := norm_add_cube_le w v
  calc
    _ ≤ K₃/2*‖w+v‖^3+K₂*‖w‖*‖v‖+K₂/2*‖v‖^2 :=
      vector_noise_drift_taylor_bound hf hK₃ h₂ h₃ x w v
    _ ≤ 2*K₃*‖w‖^3+2*K₃*‖v‖^3+K₂*‖w‖*‖v‖+K₂/2*‖v‖^2 := by
      have hh := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ K₃/2)
      nlinarith
    _ ≤ _ := by gcongr

end FourPapersCommon
