module
public import QuantitativePaper.VectorJointResponseMeasurable
public import QuantitativePaper.VectorResponseSpatialTestWithBounds

@[expose] public section

/-! Actual capped-response Itô tests with random initial disorder and
one set of spatial bounds uniform over all samples. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {F G : VectorParameter n → ℝ}

def vectorJointResponseSampleTimeData (d : VectorJointResponseTestData F G)
    (m : ℝ) (h : VectorJointBackwardBounds F G m)
    (c Q : ℝ) (hc : 0<c) (b : ℝ≥0) (hb : (b : ℝ)<Q) :
    TimeFTCData (VectorDisorderBrownianSample n) (Field n) b := by
  let A := (h.responsePower : ℝ)
  let B := (h.potentialPower : ℝ)
  let K := (n : ℝ)*A^2/2+|m| * A*B
  let J := (n : ℝ)*A^3/2+|m| * (A^2*B+A*B^2)
  have hK : 0≤K := by dsimp [K,A,B]; positivity
  have hJ : 0≤J := by dsimp [J,A,B]; positivity
  let test (p : Couplings n×ℝ) :=
    vectorResponseTimeDataWithBounds (d.fieldData p) m c Q hc b hb (h.fieldBounds p)
  refine {
    f := fun r sample x=>vectorCappedResponse (fun y=>F (sample.1,y))
      (fun y=>G (sample.1,y)) m c Q b r x
    ft := fun r sample x=>vectorCappedResponseTimeField (fun y=>F (sample.1,y))
      (fun y=>G (sample.1,y)) m c Q b r x
    bound := ⟨c*K,mul_nonneg hc.le hK⟩
    spatialLip := ⟨c*J,mul_nonneg hc.le hJ⟩
    f_measurable := ?_
    ft_measurable := ?_
    f_continuous := ?_
    derivative := ?_
    ft_continuous := ?_
    ft_bound := ?_
    ft_lipschitz := ?_ }
  · simpa only [Function.comp_def] using
      (d.measurable_cappedResponse_parameter m c Q b).comp
        (show Measurable (fun z : ℝ×(VectorDisorderBrownianSample n×Field n)=>
          (z.1,(z.2.1.1,z.2.2))) from by fun_prop)
  · simpa only [Function.comp_def] using
      (d.measurable_cappedResponseTimeField_parameter m c Q b).comp
        (show Measurable (fun z : ℝ×(VectorDisorderBrownianSample n×Field n)=>
          (z.1,(z.2.1.1,z.2.2))) from by fun_prop)
  · intro sample x
    exact (test sample.1).f_continuous sample x
  · intro sample x r hr
    exact (test sample.1).derivative sample x r hr
  · intro sample
    exact (test sample.1).ft_continuous sample
  · intro r hr sample x
    exact (test sample.1).ft_bound r hr sample x
  · intro r hr sample
    exact (test sample.1).ft_lipschitz r hr sample

def vectorJointResponseSampleSpatialTest (d : VectorJointResponseTestData F G)
    (m : ℝ) (h : VectorJointBackwardBounds F G m) (c Q b : ℝ)
    (X : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (hX : ∀ sample,Continuous (fun r=>X r sample))
    (hXa : StronglyAdapted (vectorBrownianFiltration n) X) :
    VectorSpatialItoTest (fun r sample x=>vectorCappedResponse (fun y=>F (sample.1,y))
      (fun y=>G (sample.1,y)) m c Q b r x) X := by
  have hp (sample : VectorDisorderBrownianSample n) :
      Continuous (fun r : ℝ≥0=>(vectorResponseCapVariance c Q b r,X r sample)) := by
    unfold vectorResponseCapVariance
    fun_prop
  refine {
    firstBound := h.responsePower
    secondBound := h.responsePower^2
    thirdBound := h.responsePower^3
    measurable := ?_
    regularity := ?_
    first_le := ?_
    second_le := ?_
    third_le := ?_
    adapted_first := ?_
    adapted_second := ?_
    continuous_first_path := ?_
    continuous_trace_path := ?_ }
  · intro r
    exact (h.responseRegularity (vectorResponseCapVariance c Q b r)).continuous.measurable.comp
      (show Measurable (fun z : VectorDisorderBrownianSample n×Field n=>(z.1.1,z.2)) from by fun_prop)
  · intro r sample
    exact (h.fieldBounds sample.1).responseRegularity (vectorResponseCapVariance c Q b r)
  · intro r sample x
    rw [←norm_iteratedFDeriv_one]
    change ‖iteratedFDeriv ℝ 1 (vectorStepResponse (vectorResponseCapVariance c Q b r)
      m (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y))) x‖≤(h.responsePower : ℝ)
    simpa only [pow_one,VectorJointBackwardBounds.fieldBounds] using (h.fieldBounds sample.1).responseJets
      (vectorResponseCapVariance c Q b r) 1 le_rfl (by omega) x
  · intro r sample x
    exact (h.fieldBounds sample.1).responseJets (vectorResponseCapVariance c Q b r)
      2 (by omega) (by omega) x
  · intro r sample x
    exact (h.fieldBounds sample.1).responseJets (vectorResponseCapVariance c Q b r)
      3 (by omega) le_rfl x
  · intro r q
    change Measurable[vectorBrownianFiltration n q] (fun sample=>fderiv ℝ
      (vectorStepResponse (vectorResponseCapVariance c Q b r) m
        (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y))) (X q sample))
    simpa only [Function.comp_def] using
      (d.continuous_response_first_parameter m (vectorResponseCapVariance c Q b r)).measurable.comp
        ((stronglyMeasurable_initialVectorDisorder n q).measurable.prodMk (hXa q).measurable)
  · intro r q
    change Measurable[vectorBrownianFiltration n q] (fun sample=>vectorHessian
      (vectorStepResponse (vectorResponseCapVariance c Q b r) m
        (fun y=>F (sample.1,y)) (fun y=>G (sample.1,y))) (X q sample))
    simpa only [Function.comp_def] using
      (d.continuous_response_hessian_parameter m (vectorResponseCapVariance c Q b r)).measurable.comp
        ((stronglyMeasurable_initialVectorDisorder n q).measurable.prodMk (hXa q).measurable)
  · intro sample
    change Continuous (fun r : ℝ≥0=>fderiv ℝ
      (vectorStepResponse (vectorResponseCapVariance c Q b r) m (fun y=>F (sample.1,y))
        (fun y=>G (sample.1,y))) (X r sample))
    simpa only [Function.comp_def] using
      ((d.fieldData sample.1).continuous_response_first m).comp (hp sample)
  · intro sample
    change Continuous (fun r : ℝ≥0=>vectorBilinearTrace (vectorHessian
      (vectorStepResponse (vectorResponseCapVariance c Q b r) m (fun y=>F (sample.1,y))
        (fun y=>G (sample.1,y))) (X r sample)))
    simpa only [Function.comp_def] using
      ((d.fieldData sample.1).continuous_response_trace m).comp (hp sample)

end QuantitativePaper
