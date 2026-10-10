module
public import QuantitativePaper.VectorControlDerivative
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Actual uniform quadratic remainders for fixed vector controls, obtained
from the dimension-only terminal Hessian bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorTerminalGradient_lipschitz (β t : ℝ) (p : Couplings n × ℝ) :
    LipschitzWith (n : ℝ≥0) (vectorTerminalGradient n β t p) := by
  have he : vectorTerminalGradient n β t p = vectorMagnetization
      (Paper.parisiGridRSBScheme (Paper.diracOverlap 0 (by simp)) 0) β t p 0 :=
    funext (vectorTerminalGradient_eq_magnetization β t p)
  rw [he]
  exact vectorMagnetization_lipschitz _ β t p 0

theorem vectorAffineControlDerivative_parameter_sub_le (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n)
    (hA : IsVectorParisiControl A) (a b : ℝ) (sample : VectorDisorderBrownianSample n) :
    ‖vectorAffineControlDerivative μ ν β t A a sample-
      vectorAffineControlDerivative μ ν β t A b sample‖ ≤
      4*(n : ℝ)^2*((1-t)*β^2)^2*‖a-b‖ := by
  let c := (1-t)*β^2
  let X := vectorControlledState c μ A 1 sample
  let W := vectorControlledState c ν A 1 sample-X
  have hW : ‖W‖ ≤ 2*|c| *Real.sqrt (n : ℝ) := norm_vectorControlledState_sub_le c μ ν A hA sample
  have hG := (vectorTerminalGradient_lipschitz (n := n) β t sample.1).dist_le_mul (X+a • W) (X+b • W)
  have he : X+a • W-(X+b • W)=(a-b) • W := by module
  rw [dist_eq_norm,dist_eq_norm,he,norm_smul,Real.norm_eq_abs,NNReal.coe_natCast] at hG
  unfold vectorAffineControlDerivative
  dsimp only
  change ‖(inner ℝ (vectorTerminalGradient n β t sample.1 (X+a • W)) W-_)-
      (inner ℝ (vectorTerminalGradient n β t sample.1 (X+b • W)) W-_)‖ ≤ _
  rw [sub_sub_sub_cancel_right,← inner_sub_left]
  calc
    _ ≤ ‖vectorTerminalGradient n β t sample.1 (X+a • W)-
        vectorTerminalGradient n β t sample.1 (X+b • W)‖*‖W‖ := norm_inner_le_norm _ _
    _ ≤ ((n : ℝ)*(|a-b| *(2*|c| *Real.sqrt (n : ℝ))))*(2*|c| *Real.sqrt (n : ℝ)) :=
      mul_le_mul (hG.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hW (abs_nonneg _)) (Nat.cast_nonneg n))) hW
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [Real.norm_eq_abs]
      calc
        _ = 4*(n : ℝ)*|c|^2*(Real.sqrt (n : ℝ))^2*|a-b| := by ring
        _ = _ := by rw [sq_abs,Real.sq_sqrt (Nat.cast_nonneg n)]; ring

theorem vectorAffineControlPayoff_remainder_le (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n)
    (hA : IsVectorParisiControl A) (lam : ℝ) (hlam : 0 ≤ lam)
    (sample : VectorDisorderBrownianSample n) :
    ‖vectorAffineControlPayoff μ ν β t A lam sample-
      vectorAffineControlPayoff μ ν β t A 0 sample-
      lam*vectorAffineControlDerivative μ ν β t A 0 sample‖ ≤
      4*(n : ℝ)^2*((1-t)*β^2)^2*lam^2 := by
  let f := fun r => vectorAffineControlPayoff μ ν β t A r sample-
    r*vectorAffineControlDerivative μ ν β t A 0 sample
  let d := fun r => vectorAffineControlDerivative μ ν β t A r sample-
    vectorAffineControlDerivative μ ν β t A 0 sample
  have hf : ∀r ∈ Icc (0 : ℝ) lam,HasDerivWithinAt f (d r) (Icc (0 : ℝ) lam) r := by
    intro r _
    have hl : HasDerivAt (fun a => a*vectorAffineControlDerivative μ ν β t A 0 sample)
        (vectorAffineControlDerivative μ ν β t A 0 sample) r := by
      simpa only [id_eq,one_mul] using (hasDerivAt_id r).mul_const _
    exact ((hasDerivAt_vectorAffineControlPayoff μ ν β t A r sample).sub hl).hasDerivWithinAt
  have hb : ∀r ∈ Ico (0 : ℝ) lam,‖d r‖ ≤ 4*(n : ℝ)^2*((1-t)*β^2)^2*lam := by
    intro r hr
    have hh := vectorAffineControlDerivative_parameter_sub_le μ ν β t A hA r 0 sample
    rw [sub_zero,Real.norm_of_nonneg hr.1] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hr.2.le (by positivity))
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hf hb lam ⟨hlam,le_rfl⟩
  change ‖(vectorAffineControlPayoff μ ν β t A lam sample-
      lam*vectorAffineControlDerivative μ ν β t A 0 sample)-
    (vectorAffineControlPayoff μ ν β t A 0 sample-
      0*vectorAffineControlDerivative μ ν β t A 0 sample)‖ ≤
      (4*(n : ℝ)^2*((1-t)*β^2)^2*lam)*(lam-0) at hh
  convert hh using 1
  · congr 1; ring
  · ring

end QuantitativePaper
