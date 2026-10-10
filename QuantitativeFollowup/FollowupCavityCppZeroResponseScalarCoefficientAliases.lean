module
public import QuantitativeFollowup.ScalarResponseSamples
public import QuantitativeFollowup.ScalarScoreConditioning
public import QuantitativeFollowup.FollowupCavitySignedResponseScalarDoubleKernels

@[expose] public section

/-! Exact scalar coefficient interfaces for the native cavity response.
The signed-response kernels reverse the two scalar time arguments relative
  to `scalarResponseCoefficient`. Terminal-spin factors are retained under
  their true marked law and removed only by the proved past conditioning. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open Paper FRSB
set_option autoImplicit false
set_option maxHeartbeats 800000

 theorem scalarResponseKernel3_eq_cavitySignedScalarKernelOne (β : ℝ)
    (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    scalarResponseKernel3 β μ p r ell = cavitySignedScalarKernelOne β μ r p := rfl

 theorem scalarResponseKernel4_eq_cavitySignedScalarKernelMarked (β : ℝ)
    (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    scalarResponseKernel4 β μ p r ell = cavitySignedScalarKernelMarked β hβ μ r p :=
  (scalarResponseKernel4_eq_marked β hβ μ p r ell).symm

 theorem scalarResponseKernel6_eq_cavitySignedScalarKernelTriple (β : ℝ)
    (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    scalarResponseKernel6 β μ p r ell = cavitySignedScalarKernelTriple β μ (r,ell) p := rfl

 theorem scalarResponseCoefficient3_eq_cavitySignedScalarKernelOne (β : ℝ)
    (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    scalarResponseCoefficient 3 β μ p r ell = cavitySignedScalarKernelOne β μ r p :=
  scalarResponseKernel3_eq_cavitySignedScalarKernelOne β μ p r ell

 theorem scalarResponseCoefficient4_eq_cavitySignedScalarKernelMarked (β : ℝ)
    (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    scalarResponseCoefficient 4 β μ p r ell = cavitySignedScalarKernelMarked β hβ μ r p :=
  scalarResponseKernel4_eq_cavitySignedScalarKernelMarked β hβ μ p r ell

 theorem scalarResponseCoefficient6_eq_cavitySignedScalarKernelTriple (β : ℝ)
    (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    scalarResponseCoefficient 6 β μ p r ell = cavitySignedScalarKernelTriple β μ (r,ell) p :=
  scalarResponseKernel6_eq_cavitySignedScalarKernelTriple β μ p r ell

 theorem integral_scalarResponseSample3_eq_cavitySignedScalarKernelOne (β : ℝ)
    (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    (∫ z, scalarResponseSample 3 β μ p r ell z ∂scalarMarkedSpinLaw β hβ μ) =
      cavitySignedScalarKernelOne β μ r p := by
  rw [integral_scalarResponseSample, scalarResponseCoefficient3_eq_cavitySignedScalarKernelOne]

 theorem integral_scalarResponseSample4_eq_cavitySignedScalarKernelMarked (β : ℝ)
    (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    (∫ z, scalarResponseSample 4 β μ p r ell z ∂scalarMarkedSpinLaw β hβ μ) =
      cavitySignedScalarKernelMarked β hβ μ r p := by
  rw [integral_scalarResponseSample,
    scalarResponseCoefficient4_eq_cavitySignedScalarKernelMarked β hβ μ p r ell]

 theorem integral_scalarResponseSample6_eq_cavitySignedScalarKernelTriple (β : ℝ)
    (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    (∫ z, scalarResponseSample 6 β μ p r ell z ∂scalarMarkedSpinLaw β hβ μ) =
      cavitySignedScalarKernelTriple β μ (r,ell) p := by
  rw [integral_scalarResponseSample, scalarResponseCoefficient6_eq_cavitySignedScalarKernelTriple]

 theorem integral_scalarMarkedSpinLaw_mean_curvature_sign_eq_kernel1 (β : ℝ)
    (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    (∫ z, M β μ p z.1 * C β μ p z.1 * Paper.spinSign z.2
      ∂scalarMarkedSpinLaw β hβ μ) = scalarResponseKernel1 β μ p r ell :=
  integral_scalarMarkedSpinLaw_mean_curvature_sign β hβ μ p

 theorem integral_scalarMarkedSpinLaw_mean_curvature_sign_eq_coefficient1 (β : ℝ)
    (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    (∫ z, M β μ p z.1 * C β μ p z.1 * Paper.spinSign z.2
      ∂scalarMarkedSpinLaw β hβ μ) = scalarResponseCoefficient 1 β μ p r ell :=
  integral_scalarMarkedSpinLaw_mean_curvature_sign_eq_kernel1 β hβ μ p r ell

end QuantitativeFollowup
