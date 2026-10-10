module
public import QuantitativePaper.VectorJointBackwardBounds
public import QuantitativePaper.VectorResponseCap

@[expose] public section

/-! Genuine joint measurability of the backward response tests in time,
initial disorder, and field. The actual partial derivatives are used. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ContDiff BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {F G : VectorParameter n → ℝ}

theorem VectorJointResponseTestData.continuous_response_first_parameter
    (d : VectorJointResponseTestData F G) (m v : ℝ) :
    Continuous (fun p : VectorParameter n=>fderiv ℝ
      (vectorStepResponse v m (fun x=>F (p.1,x)) (fun x=>G (p.1,x))) p.2) :=
  (contDiff_fieldSlice_fderiv (vectorJointResponse F G v m)
    ((d.jointBounds m).responseRegularity v |>.of_le (by norm_num : (1 : ℕ∞ω)+1≤3))).continuous

theorem VectorJointResponseTestData.continuous_response_hessian_parameter
    (d : VectorJointResponseTestData F G) (m v : ℝ) :
    Continuous (fun p : VectorParameter n=>vectorHessian
      (vectorStepResponse v m (fun x=>F (p.1,x)) (fun x=>G (p.1,x))) p.2) :=
  continuous_fieldSlice_hessian (vectorJointResponse F G v m)
    ((d.jointBounds m).responseRegularity v |>.of_le (by norm_num))

theorem VectorJointResponseTestData.continuous_response_trace_parameter
    (d : VectorJointResponseTestData F G) (m v : ℝ) :
    Continuous (fun p : VectorParameter n=>vectorBilinearTrace (vectorHessian
      (vectorStepResponse v m (fun x=>F (p.1,x)) (fun x=>G (p.1,x))) p.2)) := by
  unfold vectorBilinearTrace
  apply continuous_finsetSum
  intro l _
  exact (show Continuous (fun H : Field n→L[ℝ] Field n→L[ℝ] ℝ=>
    H (EuclideanSpace.single l (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ))) from by fun_prop).comp
      (d.continuous_response_hessian_parameter m v)

theorem VectorJointResponseTestData.continuous_potential_gradient_parameter
    (d : VectorJointResponseTestData F G) (m v : ℝ) :
    Continuous (fun p : VectorParameter n=>gradient
      (vectorColeHopfStep v m (fun x=>F (p.1,x))) p.2) := by
  have hh := (contDiff_fieldSlice_fderiv (vectorJointColeHopf F v m)
    ((d.jointBounds m).potentialRegularity v |>.of_le (by norm_num : (1 : ℕ∞ω)+1≤3))).continuous
  exact (InnerProductSpace.toDual ℝ (Field n)).symm.continuous.comp hh

theorem VectorJointResponseTestData.continuous_generator_parameter
    (d : VectorJointResponseTestData F G) (m v : ℝ) :
    Continuous (fun p : VectorParameter n=>vectorLinearBackwardGenerator
      (vectorStepResponse v m (fun x=>F (p.1,x)) (fun x=>G (p.1,x)))
      (vectorColeHopfStep v m (fun x=>F (p.1,x))) m p.2) := by
  exact ((d.continuous_response_trace_parameter m v).div_const 2).add
    ((d.continuous_response_first_parameter m v).clm_apply
      ((d.continuous_potential_gradient_parameter m v).const_smul m))

theorem VectorJointResponseTestData.measurable_cappedResponse_parameter
    (d : VectorJointResponseTestData F G) (m c Q b : ℝ) :
    Measurable (fun z : ℝ×VectorParameter n=>
      vectorCappedResponse (fun x=>F (z.2.1,x)) (fun x=>G (z.2.1,x)) m c Q b z.1 z.2.2) := by
  change Measurable (Function.uncurry (fun r (p : VectorParameter n)=>
    vectorCappedResponse (fun x=>F (p.1,x)) (fun x=>G (p.1,x)) m c Q b r p.2))
  apply measurable_uncurry_of_continuous_of_measurable
  · intro p
    simpa only [Function.comp_def,id_eq] using
      ((d.fieldData p.1).continuous_cappedResponse m c Q b).comp
        (continuous_id.prodMk (continuous_const (y:=p.2)))
  · intro r
    exact ((d.jointBounds m).responseRegularity (vectorResponseCapVariance c Q b r)).continuous.measurable

theorem VectorJointResponseTestData.measurable_cappedResponseTimeField_parameter
    (d : VectorJointResponseTestData F G) (m c Q b : ℝ) :
    Measurable (fun z : ℝ×VectorParameter n=>
      vectorCappedResponseTimeField (fun x=>F (z.2.1,x)) (fun x=>G (z.2.1,x)) m c Q b z.1 z.2.2) := by
  change Measurable (Function.uncurry (fun r (p : VectorParameter n)=>
    vectorCappedResponseTimeField (fun x=>F (p.1,x)) (fun x=>G (p.1,x)) m c Q b r p.2))
  apply measurable_uncurry_of_continuous_of_measurable
  · intro p
    simpa only [Function.comp_def,id_eq] using
      ((d.fieldData p.1).continuous_cappedResponseTimeField m c Q b).comp
        (continuous_id.prodMk (continuous_const (y:=p.2)))
  · intro r
    exact (continuous_const.mul
      (d.continuous_generator_parameter m (vectorResponseCapVariance c Q b r))).measurable

end QuantitativePaper
