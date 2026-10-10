module
public import QuantitativeFollowup.FollowupCavitySignedResponseOriginalIntegrability

@[expose] public section

/-! Actual integrability of all diagonal, explicit, score and last-Hessian
pieces needed to add the native signed-response integrals. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

private theorem kernel_norm (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) (x : ℝ) (hx : x^2≤Gamma β0 μ r*Gamma β0 μ p) : ‖x‖≤1 := by
  have hp : Gamma β0 μ r*Gamma β0 μ p≤1 :=
    (mul_le_mul (scalarGamma_le_one β0 μ r r.property) (scalarGamma_le_one β0 μ p p.property)
      (scalarGamma_nonneg β0 μ p) zero_le_one).trans_eq (one_mul (1:ℝ))
  have hs := hx.trans hp
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs x,abs_nonneg x]

def cavitySignedResponseT3Explicit (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a β0 : ℝ) (p : Paper.Overlap) : ℝ :=
  2*(∫l,cavitySignedScalarStrictFutureKernel β0 μ p l*
    cavitySignedResponseMixedHessianMoment D μ a p l ∂parisiFreeMeasure μ a)

theorem integrable_cavitySignedResponseT3Explicit (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) :
    Integrable (cavitySignedResponseT3Explicit D μ a β0) (parisiFreeMeasure μ a) := by
  let F := fun z : Paper.Overlap×Paper.Overlap=>cavitySignedScalarStrictFutureKernel β0 μ z.1 z.2*
    cavitySignedResponseMixedHessianMoment D μ a z.1 z.2
  have hF := (measurable_cavitySignedScalarStrictFutureKernel β0 hβ0 μ).mul
    (measurable_cavitySignedResponseMixedHessianMoment D μ a)
  have hi : Integrable F ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) := by
    apply (integrable_const 1).mono' hF.aestronglyMeasurable
    exact .of_forall fun z=>by
      change ‖cavitySignedScalarStrictFutureKernel β0 μ z.1 z.2*
        cavitySignedResponseMixedHessianMoment D μ a z.1 z.2‖≤1
      rw [norm_mul]
      exact (mul_le_mul (kernel_norm β0 μ z.1 z.2 _
        (cavitySignedScalarStrictFutureKernel_square_le β0 μ z.1 z.2))
        (norm_cavitySignedResponseMixedHessianMoment_le D μ a z.1 z.2)
        (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  exact hi.integral_prod_left.const_mul 2

theorem integrable_cavitySignedResponseT3LastHessian (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) :
    Integrable (cavitySignedResponseT3LastHessian D μ a β0) (parisiFreeMeasure μ a) := by
  have hmap : Continuous (fun z : Paper.Overlap×Paper.Overlap=>((z.2,z.1),z.2)) :=
    (continuous_snd.prodMk continuous_fst).prodMk continuous_snd
  have hK := ((continuous_cavitySignedScalarKernelTriple β0 hβ0 μ).comp hmap).measurable
  let F := fun z : Paper.Overlap×Paper.Overlap=>cavitySignedScalarKernelTriple β0 μ (z.2,z.1) z.2*
    cavitySignedResponseMixedHessianMoment D μ a z.1 z.2
  have hF := hK.mul (measurable_cavitySignedResponseMixedHessianMoment D μ a)
  have hi : Integrable F ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) := by
    apply (integrable_const 1).mono' hF.aestronglyMeasurable
    exact .of_forall fun z=>by
      change ‖cavitySignedScalarKernelTriple β0 μ (z.2,z.1) z.2*
        cavitySignedResponseMixedHessianMoment D μ a z.1 z.2‖≤1
      rw [norm_mul]
      exact (mul_le_mul (kernel_norm β0 μ (min z.2 z.1) z.2 _
        (cavitySignedScalarKernelTriple_square_le β0 μ z.2 z.1 z.2))
        (norm_cavitySignedResponseMixedHessianMoment_le D μ a z.1 z.2)
        (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  exact hi.integral_prod_right.const_mul 2

theorem integrable_cavitySignedResponseT3Score (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) (ha : a∈Icc (0:ℝ) 1) :
    Integrable (cavitySignedResponseT3Score D μ a β0) (parisiFreeMeasure μ a) := by
  let F := fun (p l : Paper.Overlap) (z : AnisotropicDisorderBrownianSample n×Configuration n)=>
    cavitySignedScalarStrictFutureKernel β0 μ p l*
      (cavitySignedResponseScore D μ a p z*cavitySignedResponseSelfOverlap D μ l z.1)
  have hKmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×
      (AnisotropicDisorderBrownianSample n×Configuration n)=>z.1) := measurable_fst
  have hRmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×
      (AnisotropicDisorderBrownianSample n×Configuration n)=>(z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hAmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×
      (AnisotropicDisorderBrownianSample n×Configuration n)=>(z.1.2,z.2.1)) :=
    measurable_fst.snd.prodMk measurable_snd.fst
  have hF := ((measurable_cavitySignedScalarStrictFutureKernel β0 hβ0 μ).comp hKmap).mul
    (((measurable_joint_cavitySignedResponseScore D μ a).comp hRmap).mul
      ((measurable_joint_cavitySignedResponseSelfOverlap D μ).comp hAmap))
  dsimp only [Function.comp_def] at hF
  have hb (p l : Paper.Overlap) (z : AnisotropicDisorderBrownianSample n×Configuration n) : ‖F p l z‖≤4 := by
    dsimp only [F]
    rw [norm_mul,norm_mul]
    exact (mul_le_mul (kernel_norm β0 μ p l _ (cavitySignedScalarStrictFutureKernel_square_le β0 μ p l))
      (mul_le_mul (norm_cavitySignedResponseScore_le D μ a ha p z)
        (norm_cavitySignedResponseSelfOverlap_le D μ l z.1) (norm_nonneg _) (by norm_num))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one).trans_eq (by norm_num)
  have hi := integrable_bounded_double_integral_family (parisiFreeMeasure μ a) (parisiFreeMeasure μ a)
    (anisotropicMeasureSpinPathLaw D μ a) F hF 4 hb
  apply hi.congr
  exact .of_forall fun p=>by
    dsimp only [F]
    simp only [integral_const_mul,cavitySignedResponseT3Score]

theorem integrable_cavitySignedResponseT3Diagonal (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) :
    Integrable (cavitySignedResponseT3Diagonal D μ a β0) (parisiFreeMeasure μ a) := by
  have hmap : Measurable (fun p : Paper.Overlap=>(p,p)) := measurable_id.prodMk measurable_id
  have hK := (continuous_cavitySignedScalarKernelOne β0 hβ0 μ).measurable.comp hmap
  have hco : Measurable (fun p : Paper.Overlap=>(p:ℝ)) := measurable_subtype_coe
  have hCDF := (Paper.parisiCDF_measurable μ).comp hco
  have hV := (continuous_cavitySignedScalarVariance β0 hβ0 μ).measurable
  have hCoef := (hK.const_mul 4).add ((((measurable_const (a:=(1:ℝ))).sub hCDF).const_mul 2).mul hV)
  have hB := (measurable_cavitySignedResponseMixedHessianMoment D μ a).comp hmap
  have hm := (hV.mul (measurable_cavitySignedResponseHessianTraceMoment D μ a)).add (hCoef.mul hB)
  let B := anisotropicProcessCovarianceEnergyBound (Finset.univ : Finset (Fin n))/(n:ℝ)^2
  apply (integrable_const (4+6*B)).mono' hm.aestronglyMeasurable
  exact .of_forall fun p=>by
    change ‖cavitySignedResponseT3Diagonal D μ a β0 p‖≤4+6*B
    have hp := cavitySignedResponseT3Diagonal_point_bound D μ a β0 hβ0 p
    rw [Real.norm_of_nonneg hp.1]
    have hjb := norm_cavitySignedResponseCovarianceMoment_le D μ a Finset.univ p
    simp only [Finset.card_univ,Fintype.card_fin] at hjb
    rw [Real.norm_of_nonneg (cavitySignedResponseCovarianceMoment_nonneg D μ a Finset.univ p)] at hjb
    have h1 := mul_le_mul (scalarGamma_le_one β0 μ p p.property)
      (cavitySignedResponseCovarianceTraceMoment_bounds D μ a p).2
      (cavitySignedResponseCovarianceTraceMoment_bounds D μ a p).1 zero_le_one
    have h2 := mul_le_mul (scalarGamma_le_one β0 μ p p.property) hjb
      (cavitySignedResponseCovarianceMoment_nonneg D μ a Finset.univ p) zero_le_one
    simp only [one_mul] at h1 h2
    exact hp.2.trans (by change _≤4+6*B;linarith)

end QuantitativeFollowup
