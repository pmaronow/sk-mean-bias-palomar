module
public import QuantitativePaper.VectorPrefixNormalization
public import QuantitativePaper.VectorSiteCurvatureLower
public import FourPapersCommon.NormalizedProductDensityLower

@[expose] public section

/-! Conditional Gaussian curvature estimates are averaged under the actual
normalized prefix law. All product densities and normalizers are derived
from the constructed finite Gaussian history. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

def vectorPrefixSiteCurvature {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (N : ℕ) (i : Fin n) (z : VectorPrefixGaussianSpace n N) : ℝ :=
  β*(vectorFieldHessian s β t (vectorPrefixEuclideanHistory s β t N z (Fin.last N)).1
    (k+2-N) (vectorPrefixEuclideanHistory s β t N z (Fin.last N)).2
    (EuclideanSpace.single i 1)) i

theorem continuous_vectorPrefixSiteCurvature {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (N : ℕ) (i : Fin n) :
    Continuous (vectorPrefixSiteCurvature s β t N i) :=
  ((continuous_vectorFieldHessian_component s β t (k+2-N) i i).comp
    ((ContinuousLinearMap.proj (Fin.last N) :
      (Fin (N+1)→VectorState n)→L[ℝ]VectorState n).continuous.comp
      (vectorPrefixEuclideanHistory s β t N).continuous)).const_mul β

theorem abs_vectorPrefixSiteCurvature_le {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : 0 ≤ β) (N : ℕ) (i : Fin n) (z : VectorPrefixGaussianSpace n N) :
    |vectorPrefixSiteCurvature s β t N i z| ≤ β := by
  have hh := abs_sitePrefixGaussianCurvature_le s β t hβ i
      (gaussianCoordinateSplit (siteGaussianPredicate i) z).2
      (gaussianCoordinateSplit (siteGaussianPredicate i) z).1
  change |vectorPrefixSiteCurvature s β t N i
    (gaussianCoordinateJoin (siteGaussianPredicate i)
      (gaussianCoordinateSplit (siteGaussianPredicate i) z))| ≤ β at hh
  rw [gaussianCoordinateJoin_split] at hh
  exact hh

theorem integral_vectorPrefixSiteCurvature_lower {n k : ℕ} (s : RSBScheme k)
    (β t a U : ℝ) (hβ : 0 < β) (ht : t ∈ Icc 0 1)
    (ha0 : 0 ≤ a) (ha : a ≤ s.m 0) (N : ℕ) (hN : N ≤ k+2) (i : Fin n)
    (hm : 1 ≤ β*observableDepthMass s (k+2-N))
    (hin : β*prefixIncomingMass s a N ≤ max 1 U) :
    responseCurvatureConstant U ≤
      ∫z,vectorPrefixSiteCurvature s β t N i z ∂vectorPrefixEuclideanLaw s β t a N := by
  let P := SYK.standardGaussianMeasureOnEuclidean (SiteGaussianIndex (N:=N) i)
  let Q := SYK.standardGaussianMeasureOnEuclidean (SiteComplementIndex (N:=N) i)
  let G := SYK.standardGaussianMeasureOnEuclidean (VectorPrefixGaussianIndex n N)
  let J := gaussianCoordinateJoin (siteGaussianPredicate (N:=N) i)
  let V := fun z : VectorPrefixGaussianSpace n N=>
    vectorPrefixLogWeight s β t a N (vectorPrefixEuclideanHistory s β t N z)
  let H := vectorPrefixSiteCurvature s β t N i
  have hJ : Measurable J := J.measurable
  have hV : Measurable V := measurable_vectorPrefixEuclideanLogWeight s β t a N
  have hH : Continuous H := continuous_vectorPrefixSiteCurvature s β t N i
  have hmap : (P.prod Q).map J=G := siteGaussianJoin_law i
  have hI : Integrable (fun z=>Real.exp (V z)) G :=
    integrable_exp_vectorPrefixEuclideanLogWeight s β t a N hN
  have hIp : Integrable (fun z=>Real.exp (V (J z))) (P.prod Q) := by
    apply (integrable_map_measure hV.exp.aestronglyMeasurable hJ.aemeasurable).mp
    rw [hmap]
    exact hI
  have hIH : Integrable (fun z=>Real.exp (V z)*H z) G :=
    hI.mul_bdd hH.aestronglyMeasurable (.of_forall fun z=>by
      simpa only [Real.norm_eq_abs] using abs_vectorPrefixSiteCurvature_le s β t hβ.le N i z)
  have hZI : (∫z,Real.exp (V (J z)) ∂P.prod Q)=vectorOuterPartition (n:=n) s β t a := by
    rw [←integral_map hJ.aemeasurable hV.exp.aestronglyMeasurable,hmap]
    exact integral_exp_vectorPrefixEuclideanLogWeight s β t a N hN
  have hl := lower_bound_normalized_product_density P Q
    (fun z=>V (J z)) (fun z=>H (J z)) (responseCurvatureConstant U) β hIp
    (hH.comp J.continuous).aestronglyMeasurable
    (fun z=>abs_vectorPrefixSiteCurvature_le s β t hβ.le N i (J z))
    (by rw [hZI];exact vectorOuterPartition_pos s β t a)
    (fun b=>(sitePrefixGaussian_curvature_raw_lower s β t a U hβ ht ha0 ha hN i b hm hin).2.2)
  have hHI : (∫z,Real.exp (V (J z))*H (J z) ∂P.prod Q)=
      ∫z,Real.exp (V z)*H z ∂G := by
    have he := integral_map (μ:=P.prod Q) (f:=fun z=>Real.exp (V z)*H z)
      hJ.aemeasurable (hV.exp.mul hH.measurable).aestronglyMeasurable
    rw [hmap] at he
    exact he.symm
  rw [hHI,hZI] at hl
  rw [integral_vectorPrefixEuclideanLaw s β t a N hN]
  exact hl

end QuantitativePaper
