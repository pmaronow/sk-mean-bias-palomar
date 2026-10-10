module
public import QuantitativePaper.VectorItoTimeExpectation
public import QuantitativePaper.VectorFiniteTimeLipschitz
public import QuantitativePaper.VectorStepJointContinuity

@[expose] public section

/-! Concrete time and spatial Itô test data for the genuine finite-cell
vector Parisi potential. The initial disorder is fixed, allowing the
identities to be applied to an independent Gaussian heat state. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def vectorFiniteCellTimeData {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    (a : ℝ) (T : ℝ≥0) (hT : a+(T : ℝ) ≤ s.q (i+1)) :
    TimeFTCData (VectorDisorderBrownianSample n) (Field n) T := by
  let h := vectorFiniteCellTimeField_uniform_spatial_lipschitz (n := n) s β t i
  let L := Classical.choose h
  have hL := (Classical.choose_spec h).1
  have hLip := (Classical.choose_spec h).2
  refine {
    f := fun r _ x => vectorFiniteCellPotential s β t p i (a+r) x
    ft := fun r _ x => vectorFiniteCellTimeField s β t p i (a+r) x
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
      (continuous_vectorFiniteCellPotential_time_field s β t p i).measurable.comp
        (show Measurable (fun z : ℝ×(VectorDisorderBrownianSample n×Field n) =>
          (a+z.1,z.2.2)) from by fun_prop)
  · simpa only [Function.comp_def] using
      (continuous_vectorFiniteCellTimeField s β t p i hi).measurable.comp
        (show Measurable (fun z : ℝ×(VectorDisorderBrownianSample n×Field n) =>
          (a+z.1,z.2.2)) from by fun_prop)
  · intro _ x
    simpa only [Function.comp_def] using
      ((continuous_vectorFiniteCellPotential_time_field s β t p i).comp
        (show Continuous (fun r : ℝ => (a+r,x)) from by fun_prop)).continuousOn
  · intro _ x r hr
    have hh := hasDerivAt_vectorFiniteCellPotential_timeField s β t hβ ht p i (a+r)
      (by linarith [hr.2]) x
    convert! hh.comp r ((hasDerivAt_id r).const_add a) using 1 <;>
      simp only [Function.comp_def,mul_one]
  · intro _
    simpa only [Function.comp_def] using
      (continuous_vectorFiniteCellTimeField s β t p i hi).comp
        (show Continuous (fun z : ℝ×Field n => (a+z.1,z.2)) from by fun_prop)
  · intro r _ _ x
    exact norm_vectorFiniteCellTimeField_le s β t ht.le p i hi (a+r) x
  · intro r _ _
    exact hLip (a+r) p

theorem continuous_vectorFiniteCellPotential_gradient {n k : ℕ}
    (s : RSBScheme k) (β t : ℝ) (p : Couplings n×ℝ) (i : ℕ) :
    Continuous (fun z : ℝ×Field n => gradient (vectorFiniteCellPotential s β t p i z.1) z.2) := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp (continuous_pi fun l =>
    continuous_vectorFiniteCellPotential_gradient_coordinate s β t p i l)

def vectorFiniteCellSpatialTest {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (a : ℝ)
    (X : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (hX : ∀sample,Continuous (fun r => X r sample))
    (hXa : StronglyAdapted (vectorBrownianFiltration n) X) :
    VectorSpatialItoTest (fun r _ x => vectorFiniteCellPotential s β t p i (a+r) x) X := by
  let h := vectorFiniteCellPotential_uniform_field_jets (n := n) s β t i 3
  let K := Classical.choose h
  have hK := (Classical.choose_spec h).1
  have hB := (Classical.choose_spec h).2
  have hK0 : 0≤K := le_trans (by norm_num) hK
  have hC (r : ℝ) : ContDiff ℝ 3 (vectorFiniteCellPotential s β t p i r) :=
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
    exact ((hC (a+r)).continuous.measurable.comp measurable_snd)
  · intro r _
    exact hC (a+r)
  · intro r _ x
    rw [←norm_iteratedFDeriv_one]
    change ‖iteratedFDeriv ℝ 1 (vectorFiniteCellPotential s β t p i (a+r)) x‖≤K
    simpa only [pow_one] using hB (a+r) 1 (by norm_num) (by norm_num) p x
  · intro r _ x
    exact hB (a+r) 2 (by norm_num) (by norm_num) p x
  · intro r _ x
    exact hB (a+r) 3 (by norm_num) le_rfl p x
  · intro r q
    exact ((hC (a+r)).fderiv_right (m := 2) (by norm_num)).continuous.measurable.comp
      (hXa q).measurable
  · intro r q
    exact (((hC (a+r)).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuous.measurable.comp (hXa q).measurable
  · intro sample
    have hgrad := (continuous_vectorFiniteCellPotential_gradient s β t p i).comp
      (show Continuous (fun r : ℝ≥0 => (a+(r : ℝ),X r sample)) from by fun_prop)
    have hh := (InnerProductSpace.toDual ℝ (Field n)).continuous.comp hgrad
    simpa only [Function.comp_def,toDual_gradient] using hh
  · intro sample
    unfold vectorBilinearTrace
    apply continuous_finsetSum
    intro l _
    change Continuous (fun r : ℝ≥0 => directionalHessian
      (vectorFiniteCellPotential s β t p i (a+r)) (X r sample) (EuclideanSpace.single l (1 : ℝ)))
    simpa only [Function.comp_def] using
      (continuous_vectorFiniteCellPotential_hessian_diagonal s β t p i l).comp
        (show Continuous (fun r : ℝ≥0 => (a+(r : ℝ),X r sample)) from by fun_prop)

end QuantitativePaper
