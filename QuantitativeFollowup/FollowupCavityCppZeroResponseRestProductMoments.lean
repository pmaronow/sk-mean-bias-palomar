module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestObservables
public import QuantitativeFollowup.FollowupCavityCppZeroResponseSeparatedMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseScalarVarianceMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseScalarFutureCentered
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestTerminalHessian
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileGradientIntegrand
public import QuantitativeFollowup.FollowupCavityCppZeroResponseMarkedProductIntegrability

@[expose] public section

/-! Actual Hessian and future-gradient product moments at the independent
endpoint. Whole paths and terminal marks remain in the underlying law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem restProduct_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem measurable_cavityZeroRestHessianSquare (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    Measurable (cavityZeroRestHessianSquare D μ p):=by
  have hm:Measurable (fun z : AnisotropicDisorderBrownianSample n=>(p,z)):=
    measurable_const.prodMk measurable_id
  exact ((measurable_uncurry_cavityHessianSquareTrace D μ).comp hm).div_const _

theorem measurable_cavityZeroRestMixedHessian (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r p : Paper.Overlap) :
    Measurable (cavityZeroRestMixedHessian D μ r p):=
  (measurable_cavitySignedResponseMixedHessian D μ r p).div_const _

theorem measurable_cavityZeroRestTerminalHessian (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    Measurable (cavityZeroRestTerminalHessian D μ p):=by
  unfold cavityZeroRestTerminalHessian
  simp_rw [←cavitySignedResponseHessianMeanCoordinate_eq_matrix_sum]
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_of_finite (fun σ : Configuration n=>Paper.spinSign (σ i))).comp
    measurable_snd).mul (((adapted_cavitySignedResponseHessianMeanCoordinate D μ p i).mono
      ((anisotropicBrownianFiltration n).le _) le_rfl).comp measurable_fst))

theorem norm_cavityZeroRestHessianSquare_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) (z : AnisotropicDisorderBrownianSample n) :
    ‖cavityZeroRestHessianSquare D μ p z‖≤4*(n:ℝ)^2/|(n:ℝ)^2|:=by
  unfold cavityZeroRestHessianSquare
  rw [norm_div,Real.norm_eq_abs]
  exact div_le_div_of_nonneg_right (norm_cavityHessianSquareTrace_le D μ p z) (abs_nonneg _)

theorem norm_cavityZeroRestMixedHessian_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r p : Paper.Overlap) (z : AnisotropicDisorderBrownianSample n) :
    ‖cavityZeroRestMixedHessian D μ r p z‖≤(n:ℝ)^2/|(n:ℝ)^2|:=by
  unfold cavityZeroRestMixedHessian
  rw [norm_div,Real.norm_eq_abs]
  exact div_le_div_of_nonneg_right (norm_cavitySignedResponseMixedHessian_le D μ r p z) (abs_nonneg _)

theorem norm_cavityZeroRestTerminalHessian_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap)
    (z : AnisotropicDisorderBrownianSample n×Configuration n) :
    ‖cavityZeroRestTerminalHessian D μ p z‖≤
      (∑i : Fin n,cavitySignedResponseHessianMeanCoordinateBound D i)/|(n:ℝ)^2|:=by
  unfold cavityZeroRestTerminalHessian
  simp_rw [←cavitySignedResponseHessianMeanCoordinate_eq_matrix_sum]
  rw [norm_div,Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  rw [←Real.norm_eq_abs]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul,Real.norm_eq_abs (Paper.spinSign _),Paper.abs_spinSign,one_mul]
  exact norm_cavitySignedResponseHessianMeanCoordinate_le D μ p i z.1

theorem norm_cavityZeroRestFutureFieldDerivative_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p r : Paper.Overlap) (hpr:p≤r)
    (z : AnisotropicDisorderBrownianSample n) :
    ‖cavityZeroRestFutureFieldDerivative D μ p r z‖≤cavityNativeFutureGradientBound D/|(n:ℝ)|:=by
  unfold cavityZeroRestFutureFieldDerivative
  rw [norm_div,Real.norm_eq_abs]
  exact div_le_div_of_nonneg_right (norm_cavityNativeFutureGradientIntegrand_le D μ p r hpr z)
    (abs_nonneg _)

theorem cavityZeroMarked_hessian_trace_scalar_variance
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,cavityZeroRestHessianSquare D μ p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample 5 B μ p p 0 (cavityZeroMarkedSampleSplit n z).2
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 restProduct_zero_mem) μ a)=
      cavitySignedResponseHessianTraceMoment D μ a p*cavitySignedScalarVariance B μ p:=by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  have hF : Measurable (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
      cavityZeroRestHessianSquare D μ p z.1) := by
    simpa only [Function.comp_def] using (measurable_cavityZeroRestHessianSquare D μ p).comp measurable_fst
  rw [integral_cavityZeroMarked_scalarResponseSample μ n β ρ hβ hρ a
    (fun z=>cavityZeroRestHessianSquare D μ p z.1) hF 5 p p 0,
    integral_anisotropicMeasureSpinPathLaw_sample D μ a
      (fun z=>cavityZeroRestHessianSquare D μ p z)
      (measurable_cavityZeroRestHessianSquare D μ p)]
  unfold cavityZeroRestHessianSquare
  rw [integral_div]
  change cavitySignedResponseHessianTraceMoment D μ a p*
    scalarResponseKernel5 (followupCavityScalarBeta n β ρ) μ p p 0=_
  rw [scalarResponseKernel5_diagonal_eq_cavitySignedScalarVariance]

theorem cavityZeroMarked_mixed_hessian_scalar_sample
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (j : Fin 8) (p r l t : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,cavityZeroRestMixedHessian D μ t p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample j B μ p r l (cavityZeroMarkedSampleSplit n z).2
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 restProduct_zero_mem) μ a)=
      cavitySignedResponseMixedHessianMoment D μ a t p*scalarResponseCoefficient j B μ p r l:=by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  have hF : Measurable (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
      cavityZeroRestMixedHessian D μ t p z.1) := by
    simpa only [Function.comp_def] using (measurable_cavityZeroRestMixedHessian D μ t p).comp measurable_fst
  rw [integral_cavityZeroMarked_scalarResponseSample μ n β ρ hβ hρ a
    (fun z=>cavityZeroRestMixedHessian D μ t p z.1) hF j p r l,
    integral_anisotropicMeasureSpinPathLaw_sample D μ a
      (fun z=>cavityZeroRestMixedHessian D μ t p z)
      (measurable_cavityZeroRestMixedHessian D μ t p)]
  unfold cavityZeroRestMixedHessian
  rw [integral_div]
  rfl

theorem cavityZeroMarked_terminal_hessian_scalar_variance
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,cavityZeroRestTerminalHessian D μ p (cavityZeroMarkedSampleSplit n z).1*
      (scalarCenteredSquare B μ p (cavityZeroMarkedSampleSplit n z).2.1*
        M B μ p (cavityZeroMarkedSampleSplit n z).2.1*
        Paper.spinSign (cavityZeroMarkedSampleSplit n z).2.2)
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 restProduct_zero_mem) μ a)=
      cavitySignedResponseMixedHessianMoment D μ a p p*cavitySignedScalarVariance B μ p:=by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  have hm:Measurable (fun z : Paper.BrownianSample×Bool=>
      scalarCenteredSquare B μ p z.1*M B μ p z.1*Paper.spinSign z.2):=
    (((((measurable_M B μ p p.property).pow_const 2).sub measurable_const).mul
      (measurable_M B μ p p.property)).comp measurable_fst).mul
        ((measurable_of_finite Paper.spinSign).comp measurable_snd)
  rw [integral_cavityZeroMarked_product μ n β ρ hβ hρ a _ _
    (measurable_cavityZeroRestTerminalHessian D μ p) hm]
  unfold cavityZeroRestTerminalHessian
  rw [cavitySignedResponse_terminal_hessian_eq_mixed_diagonal,
    integral_scalarMarkedSpinLaw_centered_mean_sign_eq_variance]

 theorem cavityZeroMarked_future_gradient_scalar_covariance
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p r : Paper.Overlap) (hpr:p≤r) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,cavityZeroRestFutureFieldDerivative D μ p r (cavityZeroMarkedSampleSplit n z).1.1*
      (scalarCenteredSquare B μ p (cavityZeroMarkedSampleSplit n z).2.1*
        scalarFutureSquareExtended B μ p r
          (parisiPhysicalSplitState B 0 μ p (cavityZeroMarkedSampleSplit n z).2.1))
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 restProduct_zero_mem) μ a)=
      cavitySignedResponseFutureGradient D μ a p r*cavitySignedScalarFutureCovarianceKernel B μ p r:=by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  have hF:Measurable (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
    cavityZeroRestFutureFieldDerivative D μ p r z.1):=
    ((measurable_cavityNativeFutureGradientIntegrand D μ p r hpr).div_const _).comp measurable_fst
  have hG:Measurable (fun z : Paper.BrownianSample×Bool=>
      scalarCenteredSquare B μ p z.1*scalarFutureSquareExtended B μ p r
        (parisiPhysicalSplitState B 0 μ p z.1)) :=
    measurable_scalarCenteredSquare_future_extended B
      (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ p r hpr
  rw [integral_cavityZeroMarked_product μ n β ρ hβ hρ a _ _ hF hG,
    integral_anisotropicMeasureSpinPathLaw_sample D μ a
      (fun z=>cavityZeroRestFutureFieldDerivative D μ p r z)
      ((measurable_cavityNativeFutureGradientIntegrand D μ p r hpr).div_const _)]
  unfold cavityZeroRestFutureFieldDerivative
  rw [integral_div,
    integral_scalarMarked_centered_future_eq_covariance B
      (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ p r hpr]
  rfl

end QuantitativeFollowup
