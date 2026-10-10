module
public import QuantitativePaper.VectorMeanStochasticL2
public import QuantitativePaper.VectorMeasureMatrixOrder
public import FourPapersCommon.MeanSquareMoments

@[expose] public section

/-! Projection of the genuine vector stochastic identity onto a bounded
random direction known in the earlier whole past. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal ENNReal Topology BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem memLp_inner_bounded_left {P : Measure (VectorDisorderBrownianSample n)}
    (b X : VectorDisorderBrownianSample n→Field n) (hb : Measurable b)
    (hX : MemLp X 2 P) (K : ℝ≥0) (hK : ∀sample,‖b sample‖≤K) :
    MemLp (fun sample =>inner ℝ (b sample) (X sample)) 2 P := by
  apply hX.of_le_mul (hb.aestronglyMeasurable.inner hX.aestronglyMeasurable)
  exact .of_forall fun sample => (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hK sample) (norm_nonneg _))

theorem tendsto_vectorMeanLeftSum_direction_L2 (hn : 0<n) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q)
    (b : VectorDisorderBrownianSample n→Field n) (hb : Measurable b)
    (K : ℝ≥0) (hK : ∀sample,‖b sample‖≤K) :
    Tendsto (fun N =>∫sample,
      ‖inner ℝ (b sample) (vectorMeanLeftSum μ β t ht.le r q hrq N sample)-
        inner ℝ (b sample) (vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample)‖^2
        ∂vectorMeasureDisorderTilt μ β t a) atTop (𝓝 0) := by
  have := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  let U : VectorDisorderBrownianSample n→Field n := fun sample =>
    vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample
  have hU : MemLp U 2 P := (memLp_vectorMeasureSpinMean μ β t a ht.le q).sub (memLp_vectorMeasureSpinMean μ β t a ht.le r)
  have hUi := memLp_inner_bounded_left b U hb hU K hK
  have hbnd (N : ℕ) : (∫sample,
      ‖inner ℝ (b sample) (vectorMeanLeftSum μ β t ht.le r q hrq N sample)-inner ℝ (b sample) (U sample)‖^2∂P)≤
      (K:ℝ)^2*(∫sample,‖U sample-vectorMeanLeftSum μ β t ht.le r q hrq N sample‖^2∂P) := by
    have hS := memLp_inner_bounded_left b _ hb (memLp_vectorMeanLeftSum μ β t a ht.le r q hrq N) K hK
    have hSdiff := hS.sub hUi
    have hVdiff := hU.sub (memLp_vectorMeanLeftSum μ β t a ht.le r q hrq N)
    rw [←integral_const_mul]
    apply integral_mono hSdiff.integrable_norm_pow' (hVdiff.integrable_norm_pow'.const_mul _)
    intro sample
    change ‖inner ℝ (b sample) (vectorMeanLeftSum μ β t ht.le r q hrq N sample)-inner ℝ (b sample) (U sample)‖^2≤
      (K:ℝ)^2*‖U sample-vectorMeanLeftSum μ β t ht.le r q hrq N sample‖^2
    rw [←inner_sub_right]
    have hi : ‖inner ℝ (b sample) (vectorMeanLeftSum μ β t ht.le r q hrq N sample-U sample)‖≤
        K*‖U sample-vectorMeanLeftSum μ β t ht.le r q hrq N sample‖ := by
      exact ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hK sample) (norm_nonneg _))).trans_eq (by rw [norm_sub_rev])
    exact (pow_le_pow_left₀ (norm_nonneg _) hi 2).trans_eq (mul_pow _ _ _)
  apply squeeze_zero (fun N =>integral_nonneg fun _=>sq_nonneg _) hbnd
  simpa only [mul_zero] using (tendsto_vectorMeanLeftSum_L2 hn μ β t a hβ ht r q hrq).const_mul ((K:ℝ)^2)

theorem vectorMeasureHessianProcess_inner_basis (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) (b : Field n) (j : Fin n) :
    inner ℝ b (vectorMeasureHessianProcess μ β t ht q sample (EuclideanSpace.single j 1))=
      vectorMeasureHessianProcess μ β t ht q sample b j := by
  let H := vectorMeasureHessianProcess μ β t ht q sample
  have hsym (i : Fin n) : H (EuclideanSpace.single j 1) i=H (EuclideanSpace.single i 1) j :=
    vectorMeasureHessianMatrix_symmetric μ β t ht q sample i j
  have hsum := vector_linear_apply_eq_sum ((EuclideanSpace.proj j).comp H) b
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial]
  rw [show H b j=∑i : Fin n,(H (EuclideanSpace.single i 1) j)*b i from hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsym i]

end QuantitativePaper
