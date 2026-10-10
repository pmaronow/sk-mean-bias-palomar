module
public import QuantitativeFollowup.FollowupCavitySignedResponseMixedHessian
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralMatrixAlgebra
public import QuantitativePaper.VectorTraceOrder

@[expose] public section

/-! Actual all-profile field-Hessian matrix order and trace comparison.
The matrix positivity is derived from the genuine posterior covariance
sandwich, rather than supplied as an assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix FourPapersCommon QuantitativePaper
open scoped BigOperators Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128

theorem nativeAnisotropicProcessHessianMatrix_quadratic (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) (w : Field n) :
    (∑i : Fin n,∑j : Fin n,nativeAnisotropicProcessHessianMatrix D μ q sample i j*w i*w j)=
      cavitySignedResponseFieldHessian D μ q (anisotropicProcessParameter D μ q sample) w w := by
  let T := fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) (anisotropicProcessParameter D μ q sample)
  let I := anisotropicFieldInjection n
  have hw : I w=∑i : Fin n,w i • I (EuclideanSpace.single i 1) := by
    simp_rw [←map_smul]
    rw [←map_sum]
    congr 1
    ext i
    simp [EuclideanSpace.single_apply,Pi.single_apply]
  change (∑i : Fin n,∑j : Fin n,T (I (EuclideanSpace.single i 1)) (I (EuclideanSpace.single j 1))*w i*w j)=T (I w) (I w)
  rw [hw,map_sum]
  simp only [map_sum,map_smul,Finset.sum_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : T (I (EuclideanSpace.single j 1)) (I (EuclideanSpace.single i 1))=
      T (I (EuclideanSpace.single i 1)) (I (EuclideanSpace.single j 1)) :=
    ((anisotropicMeasureTailPotential_hessian_limit D μ q).2.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _
  rw [hs]
  ring

theorem nativeAnisotropicProcessHessianMatrix_posSemidef (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    (nativeAnisotropicProcessHessianMatrix D μ q sample).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using
      nativeAnisotropicProcessHessianMatrix_symmetric D μ q sample j i
  · intro v
    rw [real_matrix_quadratic_eq_sum]
    have h := nativeAnisotropicProcessHessianMatrix_quadratic D μ q sample (WithLp.toLp 2 v)
    simp only [WithLp.ofLp_toLp] at h
    rw [h]
    exact cavitySignedResponseFieldHessian_nonneg D μ q _ _

theorem nativeAnisotropicProcessSpinCovariance_posSemidef (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    (anisotropicProcessSpinCovariance D μ q sample).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using
      nativeAnisotropicProcessSpinCovariance_symmetric D μ q sample j i
  · intro v
    rw [real_matrix_quadratic_eq_sum]
    exact (anisotropicTailCovarianceQuadratic_bounds D μ q (anisotropicProcessParameter D μ q sample)
      (WithLp.toLp 2 v)).1

theorem nativeAnisotropicProcessCovariance_sub_Hessian_posSemidef (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    (anisotropicProcessSpinCovariance D μ q sample-nativeAnisotropicProcessHessianMatrix D μ q sample).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (nativeAnisotropicProcessSpinCovariance_posSemidef D μ q sample).isHermitian.sub
      (nativeAnisotropicProcessHessianMatrix_posSemidef D μ q sample).isHermitian
  · intro v
    rw [real_matrix_quadratic_eq_sum]
    simp only [Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
    have h := nativeAnisotropicProcessHessianMatrix_quadratic D μ q sample (WithLp.toLp 2 v)
    simp only [WithLp.ofLp_toLp] at h
    rw [h]
    exact sub_nonneg.mpr (anisotropicMeasureTail_covariance_bounds D μ q
      (anisotropicProcessParameter D μ q sample) (WithLp.toLp 2 v)).2

theorem cavitySignedResponse_Hessian_trace_order (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    let H := nativeAnisotropicProcessHessianMatrix D μ q sample
    let C := anisotropicProcessSpinCovariance D μ q sample
    0≤Matrix.trace (H*H) ∧ Matrix.trace (H*H)≤Matrix.trace (H*C) ∧ Matrix.trace (H*C)≤Matrix.trace (C*C) := by
  dsimp only
  let H := nativeAnisotropicProcessHessianMatrix D μ q sample
  let C := anisotropicProcessSpinCovariance D μ q sample
  have hH := nativeAnisotropicProcessHessianMatrix_posSemidef D μ q sample
  have hC := nativeAnisotropicProcessSpinCovariance_posSemidef D μ q sample
  have hD := nativeAnisotropicProcessCovariance_sub_Hessian_posSemidef D μ q sample
  refine ⟨matrix_trace_mul_nonneg H H hH hH,?_,?_⟩
  · have h := matrix_trace_mul_nonneg H (C-H) hH hD
    rw [Matrix.mul_sub,Matrix.trace_sub] at h
    exact sub_nonneg.mp h
  · have h := matrix_trace_mul_nonneg (C-H) C hD hC
    rw [Matrix.sub_mul,Matrix.trace_sub] at h
    exact sub_nonneg.mp h

end QuantitativeFollowup
