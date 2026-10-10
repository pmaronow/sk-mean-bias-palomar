module
public import HexagonPaper.PathHeatClockFactor
public import QuantitativePaper.VectorSharpMassBounds
public import Mathlib.Probability.Distributions.Gaussian.CharFun

@[expose] public section

/-! The variance factor's actual centered Gaussian law. Covariance entries
are probabilistic covariances of the pushforward, rather than assigned data.
The uniqueness theorem can identify genuine Brownian evaluation laws. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal BigOperators
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n m : ℕ}

def pathHeatVarianceLaw (v : ℝ → Fin n → ℝ) (V : Fin n → Field m)
    (z : ℝ) : Measure (Field m) :=
  (fieldGaussian n).map (pathHeatVarianceFactor v V z)

instance pathHeatVarianceLaw_isGaussian (v : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ) : IsGaussian (pathHeatVarianceLaw v V z) := by
  unfold pathHeatVarianceLaw
  infer_instance

theorem pathHeatVarianceLaw_centered (v : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ) :
    (∫ x, x ∂pathHeatVarianceLaw v V z) = 0 := by
  unfold pathHeatVarianceLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  change (∫ x, pathHeatVarianceFactor v V z x ∂fieldGaussian n) = 0
  rw [(pathHeatVarianceFactor v V z).integral_comp_id_comm IsGaussian.integrable_id,
    fieldGaussian_eq_stdGaussian,integral_id_stdGaussian,map_zero]

theorem covarianceBilin_map_fieldGaussian (A : Field n →L[ℝ] Field m)
    (j k : Fin m) :
    covarianceBilin ((fieldGaussian n).map A)
      (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) =
      gaussianLinearCovariance A j k := by
  rw [covarianceBilin_map IsGaussian.memLp_two_id,
    fieldGaussian_eq_stdGaussian,covarianceBilin_stdGaussian,innerSL_apply_apply]
  have hc (j : Fin m) (i : Fin n) :
      A.adjoint (EuclideanSpace.single j 1) i = A (EuclideanSpace.single i 1) j := by
    have h := A.adjoint_inner_right (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1)
    simpa only [EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_right,
      starRingEnd_apply,star_trivial,one_mul] using h
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i : Fin n, A.adjoint (EuclideanSpace.single k 1) i *
    A.adjoint (EuclideanSpace.single j 1) i) = _
  unfold gaussianLinearCovariance
  apply Finset.sum_congr rfl
  intro i _
  rw [hc,hc]
  ring

theorem pathHeatVarianceLaw_covariance (v : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ) (hv : ∀ i, 0 ≤ v z i) (j k : Fin m) :
    covarianceBilin (pathHeatVarianceLaw v V z)
      (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) =
      pathHeatVarianceCovariance v V z j k := by
  rw [pathHeatVarianceLaw,covarianceBilin_map_fieldGaussian,
    pathHeatVarianceFactor_covariance v V z hv]

theorem pathHeatVarianceLaw_unique (v : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ) (hv : ∀ i, 0 ≤ v z i)
    (ν : Measure (Field m)) [IsGaussian ν]
    (hmean : (∫ x, x ∂ν) = 0)
    (hcov : ∀ j k : Fin m, covarianceBilin ν
      (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) =
        pathHeatVarianceCovariance v V z j k) :
    ν = pathHeatVarianceLaw v V z := by
  apply IsGaussian.ext
  · simpa only [id_eq] using
      hmean.trans (pathHeatVarianceLaw_centered v V z).symm
  · ext x y
    rw [field_bilinear_basis_expansion,field_bilinear_basis_expansion]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hcov,pathHeatVarianceLaw_covariance v V z hv]

end HexagonPaper
