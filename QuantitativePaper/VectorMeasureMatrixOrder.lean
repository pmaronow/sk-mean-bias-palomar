module
public import QuantitativePaper.VectorMeasureLoewner
public import QuantitativePaper.VectorTraceOrder
public import QuantitativePaper.VectorMeasureHessianEnergy

@[expose] public section

/-! Literal positive semidefinite matrix order and covariance/Hessian
trace inequalities for the arbitrary-profile diffusion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Matrix
open scoped NNReal BigOperators MatrixOrder
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorMeasureHessianMatrix (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j=>(vectorMeasureHessian μ β t q sample.1
    (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample) (EuclideanSpace.single j 1)) i

theorem vectorMeasureHessianMatrix_quadratic (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) (w : Field n) :
    vectorMeasureHessianQuadratic μ β t ht q w sample=
      ∑i : Fin n,∑j : Fin n,vectorMeasureHessianMatrix μ β t ht q sample i j*w i*w j :=
  euclidean_clm_quadratic_eq_sum _ w

theorem vectorMeasureHessianMatrix_symmetric (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) (i j : Fin n) :
    vectorMeasureHessianMatrix μ β t ht q sample i j=
      vectorMeasureHessianMatrix μ β t ht q sample j i := by
  let f:=vectorMeasureTailPotential μ β t q sample.1
  let x:=vectorMeasureState μ β t ht (q : ℝ).toNNReal sample
  have hi : (hessianOperator f x (EuclideanSpace.single j 1)) i=
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
    rw [←inner_hessianOperator]
    simp only [EuclideanSpace.inner_single_right,one_mul,starRingEnd_apply,star_trivial]
  have hj : (hessianOperator f x (EuclideanSpace.single i 1)) j=
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    rw [←inner_hessianOperator]
    simp only [EuclideanSpace.inner_single_right,one_mul,starRingEnd_apply,star_trivial]
  change (hessianOperator f x (EuclideanSpace.single j 1)) i=
    (hessianOperator f x (EuclideanSpace.single i 1)) j
  rw [hi,hj]
  exact ((contDiff_vectorMeasureTailPotential μ β t ht q sample.1).contDiffAt.isSymmSndFDerivAt
    (by simp)).eq _ _

theorem vectorMeasureHessianMatrix_posSemidef (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    (vectorMeasureHessianMatrix μ β t ht q sample).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using
      vectorMeasureHessianMatrix_symmetric μ β t ht q sample j i
  · intro v
    rw [real_matrix_quadratic_eq_sum]
    exact (vectorMeasureHessianMatrix_quadratic μ β t ht q sample (WithLp.toLp 2 v)) ▸
      vectorMeasureHessianQuadratic_nonneg μ β t ht q (WithLp.toLp 2 v) sample

theorem vectorMeasure_matrix_order (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    ∀ᵐsample ∂vectorMeasureDisorderTilt (n:=n) μ β t a,
      (vectorMeasureSpinCovariance μ β t a ht.le q sample).PosSemidef ∧
      (vectorMeasureHessianMatrix μ β t ht.le q sample-
        Paper.parisiCDF μ q • vectorMeasureSpinCovariance μ β t a ht.le q sample).PosSemidef ∧
      (vectorMeasureSpinCovariance μ β t a ht.le q sample-
        vectorMeasureHessianMatrix μ β t ht.le q sample).PosSemidef := by
  filter_upwards [vectorMeasureHessian_covariance_all_directions μ β t a hβ ht q,
    vectorMeasureCovarianceQuadratic_nonneg μ β t a hβ ht q] with sample hs hn
  have hC : (vectorMeasureSpinCovariance μ β t a ht.le q sample).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      simpa only [Matrix.conjTranspose_apply,star_trivial] using
        vectorMeasureSpinCovariance_symmetric μ β t a ht.le q sample j i
    · intro v
      rw [real_matrix_quadratic_eq_sum]
      exact hn (WithLp.toLp 2 v)
  have hH:=vectorMeasureHessianMatrix_posSemidef μ β t ht.le q sample
  refine ⟨hC,?_,?_⟩
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact hH.isHermitian.sub (hC.isHermitian.smul (IsSelfAdjoint.of_nonneg (Paper.parisiCDF_nonneg μ q)))
    · intro v
      rw [real_matrix_quadratic_eq_sum]
      simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,sub_mul,Finset.sum_sub_distrib]
      simp_rw [mul_assoc,←Finset.mul_sum]
      have he:=(hs (WithLp.toLp 2 v)).1
      rw [vectorMeasureHessianMatrix_quadratic] at he
      simpa only [vectorMeasureCovarianceQuadratic,WithLp.ofLp_toLp,mul_assoc] using sub_nonneg.mpr he
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact hC.isHermitian.sub hH.isHermitian
    · intro v
      rw [real_matrix_quadratic_eq_sum]
      simp only [Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
      have he:=(hs (WithLp.toLp 2 v)).2
      rw [vectorMeasureHessianMatrix_quadratic] at he
      exact sub_nonneg.mpr he

theorem vectorMeasure_trace_covariance_order (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    ∀ᵐsample ∂vectorMeasureDisorderTilt (n:=n) μ β t a,
      let H:=vectorMeasureHessianMatrix μ β t ht.le q sample
      let C:=vectorMeasureSpinCovariance μ β t a ht.le q sample
      let m:=Paper.parisiCDF μ q
      0≤Matrix.trace (H*C) ∧ m*Matrix.trace (H*C)≤Matrix.trace (H*H) ∧
        m*Matrix.trace (C*C)≤Matrix.trace (H*C) ∧ Matrix.trace (H*C)≤Matrix.trace (C*C) := by
  filter_upwards [vectorMeasure_matrix_order μ β t a hβ ht q] with sample hs
  dsimp only
  have hH:=vectorMeasureHessianMatrix_posSemidef μ β t ht.le q sample
  refine ⟨matrix_trace_mul_nonneg _ _ hH hs.1,?_,?_,?_⟩
  · have he:=matrix_trace_mul_nonneg _ _ hH hs.2.1
    rw [Matrix.mul_sub,Matrix.mul_smul,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul] at he
    linarith
  · have he:=matrix_trace_mul_nonneg _ _ hs.2.1 hs.1
    rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul] at he
    linarith
  · have he:=matrix_trace_mul_nonneg _ _ hs.2.2 hs.1
    rw [Matrix.sub_mul,Matrix.trace_sub] at he
    linarith

end QuantitativePaper
