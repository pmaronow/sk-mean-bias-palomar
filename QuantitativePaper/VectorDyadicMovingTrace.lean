module
public import QuantitativePaper.VectorDyadicMovingHessianEnergy
public import QuantitativePaper.VectorMeanHessianTrace

@[expose] public section

/-! Expected physical Hessian traces converge at genuine upward dyadic
nodes, along the finite diffusions and their own fractional disorder tilts. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
open FourPapersCommon QuantitativeFollowup Paper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def vectorDyadicMovingTrace (μ : ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (q : Overlap) (j : ℕ) (sample : VectorDisorderBrownianSample n) : ℝ :=
  β*∑l : Fin n,(vectorDyadicMovingHessian μ β t ht q j sample
    (EuclideanSpace.single l 1)) l

theorem measurable_vectorDyadicMovingTrace (μ : ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Overlap) (j : ℕ) :
    Measurable (vectorDyadicMovingTrace (n:=n) μ β t ht q j) := by
  have he : vectorDyadicMovingTrace (n:=n) μ β t ht q j=
      fun sample=>β*∑l : Fin n,vectorDyadicHessianQuadratic μ β t ht q j
        (EuclideanSpace.single l 1) sample := by
    funext sample
    unfold vectorDyadicMovingTrace
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [vectorDyadicMovingHessian_eq_node]
    simp only [vectorDyadicHessianQuadratic,EuclideanSpace.inner_single_left,
      map_one,one_mul]
  rw [he]
  exact (Finset.measurable_sum _ (fun l _=>
    measurable_vectorDyadicHessianQuadratic μ β t ht q j (EuclideanSpace.single l 1))).const_mul β

theorem norm_vectorDyadicMovingTrace_le (μ : ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Overlap) (j : ℕ) (sample : VectorDisorderBrownianSample n) :
    ‖vectorDyadicMovingTrace μ β t ht q j sample‖ ≤ |β| * (n : ℝ)^2 := by
  unfold vectorDyadicMovingTrace
  rw [norm_mul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg β)
  calc
    ‖∑l : Fin n,(vectorDyadicMovingHessian μ β t ht q j sample
      (EuclideanSpace.single l 1)) l‖ ≤
      ∑l : Fin n,‖(vectorDyadicMovingHessian μ β t ht q j sample
        (EuclideanSpace.single l 1)) l‖ := norm_sum_le _ _
    _ ≤ ∑_l : Fin n,(n : ℝ) := by
      apply Finset.sum_le_sum
      intro l _
      exact (norm_operator_diagonal_le _ l).trans
        (norm_vectorFiniteTailHessian_le _ β t _ sample.1 _)
    _ = (n : ℝ)^2 := by simp [pow_two]

theorem tendsto_vectorDyadicMovingTrace (μ : ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Overlap) (sample : VectorDisorderBrownianSample n) :
    Tendsto (fun j=>vectorDyadicMovingTrace μ β t ht q j sample) atTop
      (𝓝 (responseHessianTrace μ β t ht q sample)) := by
  have hc : Continuous (fun H : Field n→L[ℝ]Field n=>
    β*∑l : Fin n,(H (EuclideanSpace.single l 1)) l) := by fun_prop
  simpa only [vectorDyadicMovingTrace,responseHessianTrace,Matrix.trace,Matrix.diag,
    vectorMeasureHessianMatrix,Function.comp_def] using
    (hc.tendsto _).comp (tendsto_vectorDyadicMovingHessian μ β t ht q sample)

theorem tendsto_integral_vectorDyadicMovingTrace (μ : ParisiMeasure) (β t lam : ℝ)
    (ht : t ≤ 1) (q : Overlap) :
    Tendsto (fun j=>(1/(n : ℝ))*∫sample,vectorDyadicMovingTrace (n:=n) μ β t ht q j sample
      ∂vectorFiniteDisorderTilt (parisiGridRSBScheme μ (vectorDyadicIndex j)) β t (lam/β))
      atTop (𝓝 (responseMeanHessian (n:=n) μ β t lam ht q)) := by
  have hh := tendsto_integral_vectorDyadicTilt_bounded (n:=n) μ β t (lam/β) ht
    (vectorDyadicMovingTrace μ β t ht q) (responseHessianTrace μ β t ht q)
    (|β| * (n : ℝ)^2) (by positivity)
    (fun j=>measurable_vectorDyadicMovingTrace μ β t ht q j)
    (fun j sample=>norm_vectorDyadicMovingTrace_le μ β t ht q j sample)
    (.of_forall fun sample=>tendsto_vectorDyadicMovingTrace μ β t ht q sample)
  exact hh.const_mul (1/(n : ℝ))

end QuantitativePaper
