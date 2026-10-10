module
public import QuantitativeFollowup.ScalarFinitePhysicalFields
public import QuantitativeFollowup.ScalarFiniteResponseMeasure

@[expose] public section

/-! Bounded marked-diffusion integrands for each of the eight expectation
coefficients in the literal response. Their expectations are proved from
the actual spin marginal and terminal conditional law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper FRSB
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def scalarResponseSample (j : Fin 8) (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) (z : Paper.BrownianSample×Bool) : ℝ :=
  match j.val with
  | 0 => C β μ p z.1^2
  | 1 => M β μ p z.1^2*C β μ p z.1
  | 2 => M β μ p z.1*scalarFutureSquareDerivativeExtended β μ p r
      (parisiPhysicalSplitState β 0 μ p z.1)
  | 3 => M β μ p z.1*C β μ p z.1*M β μ r z.1
  | 4 => scalarCenteredSquare β μ p z.1*Paper.spinSign z.2*M β μ r z.1
  | 5 => scalarCenteredSquare β μ p z.1*M β μ r z.1^2
  | 6 => scalarCenteredSquare β μ p z.1*M β μ r z.1*M β μ ell z.1
  | _ => scalarCenteredSquare β μ p z.1*scalarFutureSquareExtended β μ r ell
      (parisiPhysicalSplitState β 0 μ r z.1)

def scalarResponseCoefficient (j : Fin 8) (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) : ℝ :=
  match j.val with
  | 0 => scalarResponseKernel0 β μ p r ell
  | 1 => scalarResponseKernel1 β μ p r ell
  | 2 => scalarResponseKernel2 β μ p r ell
  | 3 => scalarResponseKernel3 β μ p r ell
  | 4 => scalarResponseKernel4 β μ p r ell
  | 5 => scalarResponseKernel5 β μ p r ell
  | 6 => scalarResponseKernel6 β μ p r ell
  | _ => scalarResponseKernel7 β μ p r ell

theorem measurable_scalarResponseSample (j : Fin 8) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    Measurable (scalarResponseSample j β μ p r ell) := by
  have hM : Measurable (fun z : Paper.BrownianSample×Bool=>M β μ p z.1) := (measurable_M β μ p p.property).comp measurable_fst
  have hC : Measurable (fun z : Paper.BrownianSample×Bool=>C β μ p z.1) := (measurable_C β hβ μ p.property).comp measurable_fst
  have hR : Measurable (fun z : Paper.BrownianSample×Bool=>M β μ r z.1) := (measurable_M β μ r r.property).comp measurable_fst
  fin_cases j
  · exact hC.pow_const 2
  · exact (hM.pow_const 2).mul hC
  · exact (measurable_scalarResponseKernel2_integrand β hβ μ p r ell).comp measurable_fst
  · exact (hM.mul hC).mul hR
  · exact (((hM.pow_const 2).sub measurable_const).mul
      ((measurable_of_finite Paper.spinSign).comp measurable_snd)).mul hR
  · exact (measurable_scalarResponseKernel5_integrand β hβ μ p r ell).comp measurable_fst
  · exact (measurable_scalarResponseKernel6_integrand β hβ μ p r ell).comp measurable_fst
  · exact (measurable_scalarResponseKernel7_integrand β hβ μ p r ell).comp measurable_fst

theorem norm_scalarResponseSample_le (j : Fin 8) (β : ℝ)
    (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) (z : Paper.BrownianSample×Bool) :
    ‖scalarResponseSample j β μ p r ell z‖≤1+2*Real.exp (β^2) := by
  have hB : (1:ℝ)≤1+2*Real.exp (β^2) := by linarith [Real.exp_pos (β^2)]
  have hD : 2*Real.exp (β^2)≤1+2*Real.exp (β^2) := by linarith
  fin_cases j
  · exact (scalarResponseKernel0_integrand_bound β μ p r ell z.1).trans hB
  · exact (scalarResponseKernel1_integrand_bound β μ p r ell z.1).trans hB
  · exact (scalarResponseKernel2_integrand_bound β μ p r ell z.1).trans hD
  · exact (scalarResponseKernel3_integrand_bound β μ p r ell z.1).trans hB
  · change ‖scalarCenteredSquare β μ p z.1*Paper.spinSign z.2*M β μ r z.1‖≤_
    rw [norm_mul,norm_mul,show ‖Paper.spinSign z.2‖=1 by cases z.2 <;> norm_num [Paper.spinSign],mul_one]
    exact ((mul_le_mul (scalarCenteredSquare_norm_le_one β μ p z.1)
      (scalar_M_norm_le_one β μ r z.1) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)).trans hB
  · exact (scalarResponseKernel5_integrand_bound β μ p r ell z.1).trans hB
  · exact (scalarResponseKernel6_integrand_bound β μ p r ell z.1).trans hB
  · exact (scalarResponseKernel7_integrand_bound β μ p r ell z.1).trans hB

theorem integrable_scalarResponseSample (j : Fin 8) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    Integrable (scalarResponseSample j β μ p r ell) (scalarMarkedSpinLaw β hβ μ) :=
  (integrable_const (1+2*Real.exp (β^2))).mono'
    (measurable_scalarResponseSample j β hβ μ p r ell).aestronglyMeasurable
    (.of_forall fun z=>norm_scalarResponseSample_le j β μ p r ell z)

theorem integral_scalarResponseSample (j : Fin 8) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (p r ell : Paper.Overlap) :
    (∫z,scalarResponseSample j β μ p r ell z ∂scalarMarkedSpinLaw β hβ μ)=
      scalarResponseCoefficient j β μ p r ell := by
  have hM:=measurable_M β μ p p.property
  have hC:=measurable_C β hβ μ p.property
  have hR:=measurable_M β μ r r.property
  fin_cases j
  · exact integral_scalarMarkedSpinLaw_sample β hβ μ _ (hC.pow_const 2)
  · exact integral_scalarMarkedSpinLaw_sample β hβ μ _ ((hM.pow_const 2).mul hC)
  · exact integral_scalarMarkedSpinLaw_sample β hβ μ _
      (measurable_scalarResponseKernel2_integrand β hβ μ p r ell)
  · exact integral_scalarMarkedSpinLaw_sample β hβ μ _ ((hM.mul hC).mul hR)
  · exact scalarResponseKernel4_eq_marked β hβ μ p r ell
  · exact integral_scalarMarkedSpinLaw_sample β hβ μ _
      (measurable_scalarResponseKernel5_integrand β hβ μ p r ell)
  · exact integral_scalarMarkedSpinLaw_sample β hβ μ _
      (measurable_scalarResponseKernel6_integrand β hβ μ p r ell)
  · exact integral_scalarMarkedSpinLaw_sample β hβ μ _
      (measurable_scalarResponseKernel7_integrand β hβ μ p r ell)

end QuantitativeFollowup
