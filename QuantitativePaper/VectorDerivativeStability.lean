module
public import QuantitativePaper.VectorControlStability
public import QuantitativePaper.VectorFeedbackStability

@[expose] public section

/-! Continuity of the actual fixed-control derivative along the constructed
feedback family; no derivative convergence premise is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorControlDerivativeStabilityConstant (n : ℕ) (β t : ℝ) : ℝ :=
  2*(n : ℝ)*((1-t)*β^2)^2*Real.sqrt (n : ℝ)+4*|(1-t)*β^2| * Real.sqrt (n : ℝ)

theorem vectorAffineControlDerivative_control_sub_le (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A B : ℝ≥0 → VectorDisorderBrownianSample n → Field n)
    (hA : IsVectorParisiControl A) (hB : IsVectorParisiControl B)
    (ε : ℝ) (hε : 0 ≤ ε) (sample : VectorDisorderBrownianSample n)
    (hb : ∀r ≤ (1 : ℝ≥0),‖A r sample-B r sample‖ ≤ ε) :
    ‖vectorAffineControlDerivative μ ν β t A 0 sample-vectorAffineControlDerivative μ ν β t B 0 sample‖ ≤
      vectorControlDerivativeStabilityConstant n β t*ε := by
  let c := (1-t)*β^2
  let XA := vectorControlledState c μ A 1 sample
  let XB := vectorControlledState c μ B 1 sample
  let WA := vectorControlledState c ν A 1 sample-XA
  let WB := vectorControlledState c ν B 1 sample-XB
  let GA := vectorTerminalGradient n β t sample.1 XA
  let GB := vectorTerminalGradient n β t sample.1 XB
  have hX : ‖XA-XB‖ ≤ |c| *ε := norm_vectorControlledState_control_sub_le c μ A B hA hB ε hε sample hb
  have hY := norm_vectorControlledState_control_sub_le c ν A B hA hB ε hε sample hb
  have hW : ‖WA-WB‖ ≤ 2*|c| *ε := by
    have he : WA-WB=(vectorControlledState c ν A 1 sample-vectorControlledState c ν B 1 sample)-(XA-XB) := by
      dsimp only [WA,WB]; abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  have hWA : ‖WA‖ ≤ 2*|c| *Real.sqrt (n : ℝ) := norm_vectorControlledState_sub_le c μ ν A hA sample
  have hG : ‖GA-GB‖ ≤ (n : ℝ)*|c| *ε := by
    have hh := (vectorTerminalGradient_lipschitz (n := n) β t sample.1).dist_le_mul XA XB
    rw [dist_eq_norm,dist_eq_norm,NNReal.coe_natCast] at hh
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg n)])
  have hGB : ‖GB‖ ≤ Real.sqrt (n : ℝ) := norm_vectorTerminalGradient_le β t sample.1 XB
  have hμ := norm_vectorParisiControlIntegratedCost_control_sub_le c μ A B hA hB ε hε sample hb
  have hν := norm_vectorParisiControlIntegratedCost_control_sub_le c ν A B hA hB ε hε sample hb
  have hcost : ‖(vectorParisiControlIntegratedCost c ν A sample-vectorParisiControlIntegratedCost c μ A sample)-
      (vectorParisiControlIntegratedCost c ν B sample-vectorParisiControlIntegratedCost c μ B sample)‖ ≤
      2*|c| *Real.sqrt (n : ℝ)*ε := by
    rw [show (vectorParisiControlIntegratedCost c ν A sample-vectorParisiControlIntegratedCost c μ A sample)-
      (vectorParisiControlIntegratedCost c ν B sample-vectorParisiControlIntegratedCost c μ B sample) =
      (vectorParisiControlIntegratedCost c ν A sample-vectorParisiControlIntegratedCost c ν B sample)-
      (vectorParisiControlIntegratedCost c μ A sample-vectorParisiControlIntegratedCost c μ B sample) from by ring]
    exact (norm_sub_le _ _).trans (by linarith)
  have he : inner ℝ GA WA-inner ℝ GB WB=inner ℝ (GA-GB) WA+inner ℝ GB (WA-WB) := by
    simp only [inner_sub_left,inner_sub_right]; ring
  unfold vectorAffineControlDerivative
  dsimp only
  simp only [zero_smul,add_zero]
  change ‖(inner ℝ GA WA-_)-(inner ℝ GB WB-_)‖ ≤ _
  rw [show (inner ℝ GA WA-(vectorParisiControlIntegratedCost c ν A sample-vectorParisiControlIntegratedCost c μ A sample))-
      (inner ℝ GB WB-(vectorParisiControlIntegratedCost c ν B sample-vectorParisiControlIntegratedCost c μ B sample)) =
      (inner ℝ GA WA-inner ℝ GB WB)-
        ((vectorParisiControlIntegratedCost c ν A sample-vectorParisiControlIntegratedCost c μ A sample)-
          (vectorParisiControlIntegratedCost c ν B sample-vectorParisiControlIntegratedCost c μ B sample)) from by ring]
  calc
    _ ≤ ‖inner ℝ GA WA-inner ℝ GB WB‖+2*|c| *Real.sqrt (n : ℝ)*ε :=
      (norm_sub_le _ _).trans (add_le_add le_rfl hcost)
    _ ≤ ‖GA-GB‖*‖WA‖+‖GB‖*‖WA-WB‖+2*|c| *Real.sqrt (n : ℝ)*ε := by
      rw [he]
      have hi1 : ‖inner ℝ (GA-GB) WA‖ ≤ ‖GA-GB‖*‖WA‖ := norm_inner_le_norm _ _
      have hi2 : ‖inner ℝ GB (WA-WB)‖ ≤ ‖GB‖*‖WA-WB‖ := norm_inner_le_norm _ _
      exact add_le_add ((norm_add_le _ _).trans (add_le_add hi1 hi2)) le_rfl
    _ ≤ ((n : ℝ)*|c| *ε)*(2*|c| *Real.sqrt (n : ℝ))+
        Real.sqrt (n : ℝ)*(2*|c| *ε)+2*|c| *Real.sqrt (n : ℝ)*ε := by
      gcongr
    _ = _ := by
      unfold vectorControlDerivativeStabilityConstant
      rw [show ((n : ℝ)*|c| *ε)*(2*|c| *Real.sqrt (n : ℝ)) =
        2*(n : ℝ)*|c|^2*Real.sqrt (n : ℝ)*ε from by ring,sq_abs]
      dsimp only [c]; ring

theorem integral_vectorAffineControlDerivative_control_sub_le (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A B : ℝ≥0 → VectorDisorderBrownianSample n → Field n)
    (hA : IsVectorParisiControl A) (hB : IsVectorParisiControl B)
    (ε : ℝ) (hε : 0 ≤ ε) (hb : ∀r ≤ (1 : ℝ≥0),∀sample,‖A r sample-B r sample‖ ≤ ε)
    (Z : VectorDisorderBrownianSample n → ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖ ≤ C) :
    ‖(∫sample,Z sample*vectorAffineControlDerivative μ ν β t A 0 sample ∂vectorDisorderBrownianMeasure n)-
      (∫sample,Z sample*vectorAffineControlDerivative μ ν β t B 0 sample ∂vectorDisorderBrownianMeasure n)‖ ≤
      (C : ℝ)*vectorControlDerivativeStabilityConstant n β t*ε := by
  have hiA := (integrable_vectorAffineControlDerivative μ ν β t A hA 0).bdd_mul
    hZ.aestronglyMeasurable (Eventually.of_forall hC)
  have hiB := (integrable_vectorAffineControlDerivative μ ν β t B hB 0).bdd_mul
    hZ.aestronglyMeasurable (Eventually.of_forall hC)
  have he := integral_sub hiA hiB
  rw [← he]
  have hh := norm_integral_le_of_norm_le_const (μ := vectorDisorderBrownianMeasure n)
    (C := (C : ℝ)*vectorControlDerivativeStabilityConstant n β t*ε)
    (f := fun sample => Z sample*vectorAffineControlDerivative μ ν β t A 0 sample-
      Z sample*vectorAffineControlDerivative μ ν β t B 0 sample)
    (Eventually.of_forall (fun sample => by
      rw [← mul_sub,norm_mul]
      exact (mul_le_mul (hC sample)
        (vectorAffineControlDerivative_control_sub_le μ ν β t A B hA hB ε hε sample (fun r hr => hb r hr sample))
        (norm_nonneg _) C.coe_nonneg).trans_eq (by ring)))
  simpa only [probReal_univ,mul_one] using hh

end QuantitativePaper
