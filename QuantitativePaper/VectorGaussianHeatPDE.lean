module
public import QuantitativePaper.VectorHeatSpatial
public import QuantitativePaper.VectorHeatStein

@[expose] public section

/-! The actual multidimensional Gaussian heat equation. Variance
differentiation and finite-coordinate Gaussian integration by parts are
combined with genuine commutation of the spatial Hessian and integration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem vectorBilinearTrace_vectorGaussianHeat {F : Field n → ℝ}
    (d : VectorHeatDatum F) (v : ℝ) (x : Field n) :
    vectorBilinearTrace (vectorHessian (vectorGaussianHeat F v) x)=
      ∫ z,vectorBilinearTrace (vectorHessian F (fieldShift v x z)) ∂fieldGaussian n := by
  have hi := integrable_vectorHessian_heat_input d v x
  have hie (i : Fin n) := (hi.apply_continuousLinearMap (EuclideanSpace.single i 1)).apply_continuousLinearMap
    (EuclideanSpace.single i 1)
  rw [vectorHessian_vectorGaussianHeat d v x]
  unfold vectorBilinearTrace
  rw [integral_finsetSum _ (fun i _=>hie i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.integral_apply hi,
    ContinuousLinearMap.integral_apply (hi.apply_continuousLinearMap (EuclideanSpace.single i 1))]

theorem hasDerivAt_vectorGaussianHeat_variance {F : Field n → ℝ}
    (d : VectorHeatDatum F) {v : ℝ} (hv : 0 < v) (x : Field n) :
    HasDerivAt (fun u=>vectorGaussianHeat F u x)
      (vectorBilinearTrace (vectorHessian (vectorGaussianHeat F v) x)/2) v := by
  have hs (i : Fin n) := vectorHeatShiftFirst_stein d v x i
  have hH := integrable_vectorHessian_heat_input d v x
  have hHi (i : Fin n) := (hH.apply_continuousLinearMap (EuclideanSpace.single i 1)).apply_continuousLinearMap
    (EuclideanSpace.single i 1)
  have he (z : Field n) : fderiv ℝ F (fieldShift v x z) ((1/(2*Real.sqrt v)) • z)=
      (1/(2*Real.sqrt v))*(∑ i : Fin n,z i*vectorHeatShiftFirst F v x i z) := by
    rw [map_smul,smul_eq_mul,field_clm_basis_expansion]
    simp only [EuclideanSpace.basisFun_apply,vectorHeatShiftFirst]
  have hsum : (∫ z,fderiv ℝ F (fieldShift v x z) ((1/(2*Real.sqrt v)) • z) ∂fieldGaussian n)=
      vectorBilinearTrace (vectorHessian (vectorGaussianHeat F v) x)/2 := by
    rw [show (fun z=>fderiv ℝ F (fieldShift v x z) ((1/(2*Real.sqrt v)) • z))=
      (fun z=>(1/(2*Real.sqrt v))*(∑ i : Fin n,z i*vectorHeatShiftFirst F v x i z)) from funext he,
      integral_const_mul,integral_finsetSum _ (fun i _=>(hs i).1)]
    simp_rw [(hs _).2.2]
    rw [← Finset.mul_sum,vectorBilinearTrace_vectorGaussianHeat d v x]
    unfold vectorBilinearTrace
    rw [integral_finsetSum _ (fun i _=>hHi i)]
    have hr : Real.sqrt v≠0 := (Real.sqrt_pos.mpr hv).ne'
    field_simp
  exact (hasDerivAt_vectorGaussianHeat_scale d hv x).congr_deriv hsum

end QuantitativePaper
