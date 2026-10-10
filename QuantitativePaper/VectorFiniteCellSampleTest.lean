module
public import QuantitativePaper.VectorFiniteCellJointMeasurable

@[expose] public section

/-! Concrete finite-cell Itô tests with the actual initial random disorder,
retained in the genuine enlarged vector-Wiener filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def vectorFiniteCellSampleTimeData {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    (a : ℝ) (T : ℝ≥0) (hT : a+(T : ℝ) ≤ s.q (i+1)) :
    TimeFTCData (VectorDisorderBrownianSample n) (Field n) T := by
  let h := vectorFiniteCellTimeField_uniform_spatial_lipschitz (n := n) s β t i
  let L := Classical.choose h
  have hL := (Classical.choose_spec h).1
  have hLip := (Classical.choose_spec h).2
  refine {
    f := fun r sample x => vectorFiniteCellPotential s β t sample.1 i (a+r) x
    ft := fun r sample x => vectorFiniteCellTimeField s β t sample.1 i (a+r) x
    bound := ⟨((1-t)*β^2)*(n : ℝ)/2,by positivity⟩
    spatialLip := L.toNNReal
    f_measurable := ?_
    ft_measurable := ?_
    f_continuous := ?_
    derivative := ?_
    ft_continuous := ?_
    ft_bound := ?_
    ft_lipschitz := ?_ }
  · simpa only [Function.comp_def] using
      (measurable_vectorFiniteCellPotential_time_parameter s β t i).comp
        (show Measurable (fun z : ℝ×(VectorDisorderBrownianSample n×Field n) =>
          (a+z.1,(z.2.1.1,z.2.2))) from by fun_prop)
  · simpa only [Function.comp_def] using
      (measurable_vectorFiniteCellTimeField_time_parameter s β t i hi).comp
        (show Measurable (fun z : ℝ×(VectorDisorderBrownianSample n×Field n) =>
          (a+z.1,(z.2.1.1,z.2.2))) from by fun_prop)
  · intro sample x
    simpa only [Function.comp_def] using
      ((continuous_vectorFiniteCellPotential_time_field s β t sample.1 i).comp
        (show Continuous (fun r : ℝ => (a+r,x)) from by fun_prop)).continuousOn
  · intro sample x r hr
    have hh := hasDerivAt_vectorFiniteCellPotential_timeField s β t hβ ht sample.1 i (a+r)
      (by linarith [hr.2]) x
    convert! hh.comp r ((hasDerivAt_id r).const_add a) using 1 <;> simp only [mul_one]
  · intro sample
    simpa only [Function.comp_def] using
      (continuous_vectorFiniteCellTimeField s β t sample.1 i hi).comp
        (show Continuous (fun z : ℝ×Field n => (a+z.1,z.2)) from by fun_prop)
  · intro r _ sample x
    exact norm_vectorFiniteCellTimeField_le s β t ht.le sample.1 i hi (a+r) x
  · intro r _ sample
    exact hLip (a+r) sample.1

def vectorFiniteCellSampleSpatialTest {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (a : ℝ) (X : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (hX : ∀sample,Continuous (fun r => X r sample))
    (hXa : StronglyAdapted (vectorBrownianFiltration n) X) :
    VectorSpatialItoTest (fun r sample x => vectorFiniteCellPotential s β t sample.1 i (a+r) x) X := by
  let h := vectorFiniteCellPotential_uniform_field_jets (n := n) s β t i 3
  let K := Classical.choose h
  have hK := (Classical.choose_spec h).1
  have hB := (Classical.choose_spec h).2
  have hK0 : 0≤K := le_trans (by norm_num) hK
  have hC (r : ℝ) (p : Couplings n×ℝ) : ContDiff ℝ 3 (vectorFiniteCellPotential s β t p i r) :=
    (contDiff_vectorColeHopfStep_recursion_field s β t _ _ p _).of_le (by simp)
  refine {
    firstBound := ⟨K,hK0⟩
    secondBound := ⟨K^2,by positivity⟩
    thirdBound := ⟨K^3,by positivity⟩
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
    simpa only [Function.comp_def,Function.uncurry_def] using
      (contDiff_vectorFiniteCellPotential_joint s β t i (a+r)).continuous.measurable.comp
        (show Measurable (fun z : VectorDisorderBrownianSample n×Field n => (z.1.1,z.2)) from by fun_prop)
  · intro r sample
    exact hC (a+r) sample.1
  · intro r sample x
    rw [←norm_iteratedFDeriv_one]
    change ‖iteratedFDeriv ℝ 1 (vectorFiniteCellPotential s β t sample.1 i (a+r)) x‖≤K
    simpa only [pow_one] using hB (a+r) 1 (by norm_num) (by norm_num) sample.1 x
  · intro r sample x
    exact hB (a+r) 2 (by norm_num) (by norm_num) sample.1 x
  · intro r sample x
    exact hB (a+r) 3 (by norm_num) le_rfl sample.1 x
  · intro r q
    simpa only [Function.comp_def] using
      (continuous_vectorFiniteCell_fderiv_parameter s β t i (a+r)).measurable.comp
        ((stronglyMeasurable_initialVectorDisorder n q).measurable.prodMk (hXa q).measurable)
  · intro r q
    simpa only [Function.comp_def] using
      (continuous_vectorFiniteCell_hessian_parameter s β t i (a+r)).measurable.comp
        ((stronglyMeasurable_initialVectorDisorder n q).measurable.prodMk (hXa q).measurable)
  · intro sample
    have hgrad := (continuous_vectorFiniteCellPotential_gradient s β t sample.1 i).comp
      (show Continuous (fun r : ℝ≥0 => (a+(r : ℝ),X r sample)) from by fun_prop)
    have hh := (InnerProductSpace.toDual ℝ (Field n)).continuous.comp hgrad
    simpa only [Function.comp_def,toDual_gradient] using hh
  · intro sample
    unfold vectorBilinearTrace
    apply continuous_finsetSum
    intro l _
    change Continuous (fun r : ℝ≥0 => directionalHessian
      (vectorFiniteCellPotential s β t sample.1 i (a+r)) (X r sample) (EuclideanSpace.single l (1 : ℝ)))
    simpa only [Function.comp_def] using
      (continuous_vectorFiniteCellPotential_hessian_diagonal s β t sample.1 i l).comp
        (show Continuous (fun r : ℝ≥0 => (a+(r : ℝ),X r sample)) from by fun_prop)

end QuantitativePaper
