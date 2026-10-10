module
public import HexagonPaper.CavityMovingCoefficientVarianceDisorderJoint
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-! The literal native magnetization has its genuine last-coefficient
derivative, with a jointly continuous native response vector. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ContDiff NNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

def cavityNativeTailMagnetizationVarianceDerivative
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) : Field n :=
  WithLp.toLp 2 (fun j=>fderiv ℝ (fun y=>anisotropicRestartVarianceResponse D μ g q y i) x
    (EuclideanSpace.single j 1))

theorem cavityNativeTailMagnetization_component_hasDerivAt_variance
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i j : Fin n)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (b : ℝ) (hb : 0<b) :
    HasDerivAt (fun u=>anisotropicMeasureTailMagnetization (anisotropicReplaceVariance D i u) μ q
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) j)
      (cavityNativeTailMagnetizationVarianceDerivative (anisotropicReplaceVariance D i b) μ i g q x j) b := by
  exact cavityNativeTailPotential_field_partial_hasDerivAt_variance D μ i g q x (EuclideanSpace.single j 1) b hb

theorem cavityNativeTailMagnetization_hasDerivAt_variance
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (b : ℝ) (hb : 0<b) :
    HasDerivAt (fun u=>anisotropicMeasureTailMagnetization (anisotropicReplaceVariance D i u) μ q
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x))
      (cavityNativeTailMagnetizationVarianceDerivative (anisotropicReplaceVariance D i b) μ i g q x) b := by
  let e : Field n≃L[ℝ](Fin n→ℝ):=PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>ℝ)
  have h : HasDerivAt (fun u=>e (anisotropicMeasureTailMagnetization (anisotropicReplaceVariance D i u) μ q
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x)))
      (e (cavityNativeTailMagnetizationVarianceDerivative (anisotropicReplaceVariance D i b) μ i g q x)) b := by
    apply hasDerivAt_pi.mpr
    intro j
    exact cavityNativeTailMagnetization_component_hasDerivAt_variance D μ i j g q x b hb
  have ht:=e.symm.hasFDerivAt.comp_hasDerivAt b h
  convert ht using 1
  all_goals first | rfl | simp only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply]

theorem cavityNativeTailMagnetizationVarianceDerivative_joint_continuous
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n) (q : Paper.Overlap) :
    Continuous (fun z : ({b : ℝ // 0<b}×AnisotropicDisorder n)×Field n=>
      cavityNativeTailMagnetizationVarianceDerivative (anisotropicReplaceVariance D i z.1.1.val) μ i z.1.2 q z.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n=>ℝ)).comp
  apply continuous_pi
  intro j
  exact (cavityNativeVarianceResponse_fderiv_coefficient_disorder_field_joint_continuous D μ i q).clm_apply
    (continuous_const (y:=EuclideanSpace.single j 1))

end HexagonPaper
