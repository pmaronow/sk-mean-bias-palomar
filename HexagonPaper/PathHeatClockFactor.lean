module
public import QuantitativeFollowup.GaussianCovarianceMatrix

@[expose] public section

/-! Explicit independent variance factors for finite Gaussian path samples.
Every covariance and covariance direction below is computed from the actual
linear Gaussian input. No matrix inverse or response identity is assumed. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal BigOperators
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n m : ℕ}

def pathHeatVectorMask (V : Fin n → Field m) (i : Fin n) :
    Field n →L[ℝ] Field m :=
  (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin n => ℝ) i).smulRight (V i)

def pathHeatVarianceFactor (v : ℝ → Fin n → ℝ) (V : Fin n → Field m)
    (z : ℝ) : Field n →L[ℝ] Field m :=
  ∑ i : Fin n, Real.sqrt (v z i) • pathHeatVectorMask V i

def pathHeatVarianceFactorDerivative (v dv : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ) : Field n →L[ℝ] Field m :=
  ∑ i : Fin n, (dv z i / (2 * Real.sqrt (v z i))) • pathHeatVectorMask V i

def pathHeatVarianceCovariance (v : ℝ → Fin n → ℝ) (V : Fin n → Field m)
    (z : ℝ) (j k : Fin m) : ℝ :=
  ∑ i : Fin n, v z i * V i j * V i k

def pathHeatVarianceCovarianceDerivative (dv : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ) (j k : Fin m) : ℝ :=
  ∑ i : Fin n, dv z i * V i j * V i k

theorem pathHeatVarianceFactor_basis (v : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ) (i : Fin n) :
    pathHeatVarianceFactor v V z (EuclideanSpace.single i 1) =
      Real.sqrt (v z i) • V i := by
  simp [pathHeatVarianceFactor,pathHeatVectorMask,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,PiLp.single_apply]

theorem pathHeatVarianceFactorDerivative_basis (v dv : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ) (i : Fin n) :
    pathHeatVarianceFactorDerivative v dv V z (EuclideanSpace.single i 1) =
      (dv z i / (2 * Real.sqrt (v z i))) • V i := by
  simp [pathHeatVarianceFactorDerivative,pathHeatVectorMask,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,PiLp.single_apply]

theorem hasDerivAt_pathHeatVarianceFactor (v dv : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ)
    (hv : ∀ i, 0 < v z i)
    (hdv : ∀ i, HasDerivAt (fun u => v u i) (dv z i) z) :
    HasDerivAt (pathHeatVarianceFactor v V)
      (pathHeatVarianceFactorDerivative v dv V z) z := by
  unfold pathHeatVarianceFactor pathHeatVarianceFactorDerivative
  apply HasDerivAt.fun_sum
  intro i _
  exact ((hdv i).sqrt (hv i).ne').smul_const (pathHeatVectorMask V i)

theorem pathHeatVarianceFactor_covariance (v : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ) (hv : ∀ i, 0 ≤ v z i) (j k : Fin m) :
    gaussianLinearCovariance (pathHeatVarianceFactor v V z) j k =
      pathHeatVarianceCovariance v V z j k := by
  unfold gaussianLinearCovariance pathHeatVarianceCovariance
  apply Finset.sum_congr rfl
  intro i _
  rw [pathHeatVarianceFactor_basis]
  change (Real.sqrt (v z i)*V i j)*(Real.sqrt (v z i)*V i k)=_
  calc
    _ = (Real.sqrt (v z i))^2 * V i j * V i k := by ring
    _ = _ := by rw [Real.sq_sqrt (hv i)]

theorem hasDerivAt_pathHeatVarianceCovariance (v dv : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ)
    (hdv : ∀ i, HasDerivAt (fun u => v u i) (dv z i) z) (j k : Fin m) :
    HasDerivAt (fun u => pathHeatVarianceCovariance v V u j k)
      (pathHeatVarianceCovarianceDerivative dv V z j k) z := by
  unfold pathHeatVarianceCovariance pathHeatVarianceCovarianceDerivative
  apply HasDerivAt.fun_sum
  intro i _
  exact ((hdv i).mul_const (V i j)).mul_const (V i k)

theorem pathHeatVarianceFactor_covariance_direction (v dv : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ) (hv : ∀ i, 0 < v z i) (j k : Fin m) :
    gaussianLinearCovarianceDirection (pathHeatVarianceFactor v V z)
      (pathHeatVarianceFactorDerivative v dv V z) j k =
      pathHeatVarianceCovarianceDerivative dv V z j k := by
  unfold gaussianLinearCovarianceDirection pathHeatVarianceCovarianceDerivative
  apply Finset.sum_congr rfl
  intro i _
  rw [pathHeatVarianceFactor_basis,pathHeatVarianceFactorDerivative_basis]
  change (dv z i/(2*Real.sqrt (v z i))*V i j)*(Real.sqrt (v z i)*V i k)+
    (Real.sqrt (v z i)*V i j)*(dv z i/(2*Real.sqrt (v z i))*V i k)=_
  have hs : Real.sqrt (v z i) ≠ 0 := (Real.sqrt_pos.2 (hv i)).ne'
  field_simp [hs]
  <;> ring

theorem pathHeatVarianceFactor_bilinear_contraction (v dv : ℝ → Fin n → ℝ)
    (V : Fin n → Field m) (z : ℝ) (hv : ∀ i, 0 < v z i)
    (H : Field m →L[ℝ] Field m →L[ℝ] ℝ) (hH : ∀ u w, H u w = H w u) :
    (∑ i : Fin n, H
      (pathHeatVarianceFactor v V z (EuclideanSpace.single i 1))
      (pathHeatVarianceFactorDerivative v dv V z (EuclideanSpace.single i 1))) =
      (1/2 : ℝ) * ∑ j : Fin m, ∑ k : Fin m,
        pathHeatVarianceCovarianceDerivative dv V z j k *
          H (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) := by
  rw [gaussian_covariance_bilinear_contraction _ _ H hH]
  simp only [pathHeatVarianceFactor_covariance_direction v dv V z hv]

end HexagonPaper
