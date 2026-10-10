module
public import QuantitativePaper.VectorResponseCap
public import QuantitativePaper.VectorItoIntervalExpectation

@[expose] public section

/-! Actual time fundamental-theorem data for the capped normalized Gaussian
response. All bounds are generated from its actual spatial jets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ}

def vectorResponseTimeData {f g : Field n → ℝ} (d : VectorResponseTestData f g)
    (m c Q : ℝ) (hc : 0<c) (b : ℝ≥0) (hb : (b : ℝ)<Q) :
    TimeFTCData (VectorDisorderBrownianSample n) (Field n) b := by
  let h := d.bounds m
  let A := (h.responsePower : ℝ)
  let B := (h.potentialPower : ℝ)
  let K := (n : ℝ)*A^2/2+|m| * A*B
  let J := (n : ℝ)*A^3/2+|m| * (A^2*B+A*B^2)
  have hA : 0≤A := h.responsePower.coe_nonneg
  have hB : 0≤B := h.potentialPower.coe_nonneg
  have hK : 0≤K := by positivity
  have hJ : 0≤J := by positivity
  refine {
    f := fun r _ x=>vectorCappedResponse f g m c Q b r x
    ft := fun r _ x=>vectorCappedResponseTimeField f g m c Q b r x
    bound := ⟨c*K,mul_nonneg hc.le hK⟩
    spatialLip := ⟨c*J,mul_nonneg hc.le hJ⟩
    f_measurable := ?_
    ft_measurable := ?_
    f_continuous := ?_
    derivative := ?_
    ft_continuous := ?_
    ft_bound := ?_
    ft_lipschitz := ?_ }
  · exact (d.continuous_cappedResponse m c Q b).measurable.comp
      (show Measurable (fun p : ℝ×(VectorDisorderBrownianSample n×Field n)=>(p.1,p.2.2)) from by fun_prop)
  · exact (d.continuous_cappedResponseTimeField m c Q b).measurable.comp
      (show Measurable (fun p : ℝ×(VectorDisorderBrownianSample n×Field n)=>(p.1,p.2.2)) from by fun_prop)
  · intro _ x
    exact ((d.continuous_cappedResponse m c Q b).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  · intro _ x r _
    exact hasDerivAt_vectorCappedResponse d m hc hb r x
  · intro _
    exact d.continuous_cappedResponseTimeField m c Q b
  · intro r hr _ x
    rw [vectorCappedResponseTimeField_of_le f g m c Q b r hr.2 x,norm_mul,
      norm_neg,Real.norm_of_nonneg hc.le]
    exact mul_le_mul_of_nonneg_left (vectorLinearBackwardGenerator_bound
      (vectorStepResponse (c*(Q-r)) m f g) (vectorColeHopfStep (c*(Q-r)) m f)
      m A B hA hB (h.responseJets _) (h.potentialJets _) x) hc.le
  · intro r hr _
    have hl := vectorLinearBackwardGenerator_lipschitz
      (vectorStepResponse (c*(Q-r)) m f g) (vectorColeHopfStep (c*(Q-r)) m f)
      (h.responseRegularity _) (h.potentialRegularity _) m A B
      (show 1≤A from h.responsePower_ge_one) (show 1≤B from h.potentialPower_ge_one)
      (h.responseJets _) (h.potentialJets _)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq,vectorCappedResponseTimeField_of_le f g m c Q b r hr.2 x,
      vectorCappedResponseTimeField_of_le f g m c Q b r hr.2 y,←mul_sub,abs_mul,abs_neg,abs_of_pos hc]
    change c*|vectorLinearBackwardGenerator (vectorStepResponse (c*(Q-r)) m f g)
      (vectorColeHopfStep (c*(Q-r)) m f) m x-
      vectorLinearBackwardGenerator (vectorStepResponse (c*(Q-r)) m f g)
        (vectorColeHopfStep (c*(Q-r)) m f) m y| ≤ (c*J)*dist x y
    have hh := hl.dist_le_mul x y
    rw [Real.dist_eq,Real.coe_toNNReal _ hJ] at hh
    have hh' := mul_le_mul_of_nonneg_left hh hc.le
    simpa only [J,mul_assoc] using hh'

end QuantitativePaper
