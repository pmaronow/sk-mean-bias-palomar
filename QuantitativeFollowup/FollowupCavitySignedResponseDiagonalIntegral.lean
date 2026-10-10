module
public import QuantitativeFollowup.FollowupCavitySignedResponseTraceMoments

@[expose] public section

/-! Literal diagonal part of T3, with its actual scalar variance and
field-Hessian traces. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def cavitySignedScalarVariance (β0 : ℝ) (μ : Paper.ParisiMeasure) (p : Paper.Overlap) : ℝ :=
  variance (fun ω=>M β0 μ p ω^2) canonicalBrownianMeasure

theorem continuous_cavitySignedScalarVariance (β0 : ℝ) (hβ0 : β0≠0) (μ : Paper.ParisiMeasure) :
    Continuous (cavitySignedScalarVariance β0 μ) := by
  have he : cavitySignedScalarVariance β0 μ=(fun p : Paper.Overlap=>∫ω,scalarCenteredSquare β0 μ p ω^2 ∂canonicalBrownianMeasure) := by
    funext p
    rw [cavitySignedScalarVariance,variance_eq_integral ((measurable_M β0 μ p p.property).pow_const 2).aemeasurable]
    rfl
  rw [he]
  apply continuous_of_dominated (μ:=canonicalBrownianMeasure) (bound:=fun _=>(1:ℝ))
  · intro p
    exact ((((measurable_M β0 μ p p.property).pow_const 2).sub measurable_const).pow_const 2).aestronglyMeasurable
  · intro p
    exact .of_forall fun ω=>by rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) (scalarCenteredSquare_norm_le_one β0 μ p ω)
  · exact integrable_const _
  · exact .of_forall fun ω=>(continuous_scalarCenteredSquare_parameter β0 hβ0 ω).comp
      (continuous_const.prodMk continuous_id) |>.pow 2

def cavitySignedScalarDiagonalCoefficient (β0 : ℝ) (μ : Paper.ParisiMeasure) (p : Paper.Overlap) : ℝ :=
  4*cavitySignedScalarKernelOne β0 μ p p+2*(1-Paper.parisiCDF μ p)*cavitySignedScalarVariance β0 μ p

theorem cavitySignedScalarDiagonalCoefficient_bounds (β0 : ℝ) (hβ0 : β0≠0)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    0≤cavitySignedScalarDiagonalCoefficient β0 μ p ∧
      cavitySignedScalarDiagonalCoefficient β0 μ p≤6*Gamma β0 μ p := by
  have he : cavitySignedScalarKernelOne β0 μ p p=∫ω,M β0 μ p ω^2*C β0 μ p ω∂canonicalBrownianMeasure := by
    apply integral_congr_ae
    exact .of_forall fun ω=>by ring
  have hm := scalar_M_sq_C_bound β0 hβ0 μ p p.property
  rw [←he] at hm
  have hv := scalar_square_variance_bound β0 μ p p.property
  change 0≤cavitySignedScalarVariance β0 μ p ∧ cavitySignedScalarVariance β0 μ p≤Gamma β0 μ p at hv
  have hc0 := Paper.parisiCDF_nonneg μ p
  have hc1 := Paper.parisiCDF_le_one μ p
  have hrest : 0≤1-Paper.parisiCDF μ p := sub_nonneg.mpr hc1
  unfold cavitySignedScalarDiagonalCoefficient
  constructor
  · exact add_nonneg (mul_nonneg (by norm_num) hm.1)
      (mul_nonneg (mul_nonneg (by norm_num) hrest) hv.1)
  · have hmul := mul_le_mul_of_nonneg_right (show 1-Paper.parisiCDF μ p≤1 by linarith) hv.1
    nlinarith

def cavitySignedResponseT3Diagonal (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a β0 : ℝ) (p : Paper.Overlap) : ℝ :=
  cavitySignedScalarVariance β0 μ p*cavitySignedResponseHessianTraceMoment D μ a p+
    cavitySignedScalarDiagonalCoefficient β0 μ p*cavitySignedResponseMixedHessianMoment D μ a p p

theorem cavitySignedResponseT3Diagonal_point_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) (p : Paper.Overlap) :
    0≤cavitySignedResponseT3Diagonal D μ a β0 p ∧
      cavitySignedResponseT3Diagonal D μ a β0 p≤
        Gamma β0 μ p*cavitySignedResponseCovarianceTraceMoment D μ a p+
          6*(Gamma β0 μ p*cavitySignedResponseCovarianceMoment D μ a Finset.univ p) := by
  have hv := scalar_square_variance_bound β0 μ p p.property
  change 0≤cavitySignedScalarVariance β0 μ p ∧ cavitySignedScalarVariance β0 μ p≤Gamma β0 μ p at hv
  have haH := cavitySignedResponseHessianTraceMoment_bounds D μ a p
  have hbH := cavitySignedResponseMixedHessianMoment_diagonal_bounds D μ a p
  have hc := cavitySignedScalarDiagonalCoefficient_bounds β0 hβ0 μ p
  have haC := cavitySignedResponseCovarianceTraceMoment_bounds D μ a p
  unfold cavitySignedResponseT3Diagonal
  refine ⟨add_nonneg (mul_nonneg hv.1 haH.1) (mul_nonneg hc.1 hbH.1),?_⟩
  have h1 := mul_le_mul hv.2 haH.2 haH.1 (scalarGamma_nonneg β0 μ p)
  have h2 := mul_le_mul hc.2 hbH.2 hbH.1 (mul_nonneg (by norm_num : 0≤(6:ℝ)) (scalarGamma_nonneg β0 μ p))
  simpa only [mul_assoc] using add_le_add h1 h2

theorem cavitySignedResponse_T3_diagonal_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) :
    |∫p,cavitySignedResponseT3Diagonal D μ a β0 p ∂parisiFreeMeasure μ a|≤
      cavitySignedResponseWeightedA D μ a β0+6*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  let ν := parisiFreeMeasure μ a
  let A := fun p : Paper.Overlap=>Gamma β0 μ p*cavitySignedResponseCovarianceTraceMoment D μ a p
  let J := fun p : Paper.Overlap=>Gamma β0 μ p*cavitySignedResponseCovarianceMoment D μ a Finset.univ p
  let B := anisotropicProcessCovarianceEnergyBound (Finset.univ : Finset (Fin n))/(n:ℝ)^2
  have hΓ : Measurable (fun p : Paper.Overlap=>Gamma β0 μ p) :=
    ((continuousOn_Gamma β0 hβ0 μ).comp_continuous continuous_subtype_val (fun p=>p.property)).measurable
  have hA : Integrable A ν := (integrable_const (4:ℝ)).mono'
    (hΓ.mul (measurable_cavitySignedResponseCovarianceTraceMoment D μ a)).aestronglyMeasurable
    (.of_forall fun p=>by
      rw [norm_mul,Real.norm_of_nonneg (scalarGamma_nonneg β0 μ p),Real.norm_of_nonneg (cavitySignedResponseCovarianceTraceMoment_bounds D μ a p).1]
      exact (mul_le_mul (scalarGamma_le_one β0 μ p p.property)
        (cavitySignedResponseCovarianceTraceMoment_bounds D μ a p).2
        (cavitySignedResponseCovarianceTraceMoment_bounds D μ a p).1 zero_le_one).trans_eq (by norm_num))
  have hJ : Integrable J ν := (integrable_const B).mono'
    (hΓ.mul (measurable_cavitySignedResponseCovarianceMoment D μ a Finset.univ)).aestronglyMeasurable
    (.of_forall fun p=>by
      rw [norm_mul,Real.norm_of_nonneg (scalarGamma_nonneg β0 μ p)]
      have hb := norm_cavitySignedResponseCovarianceMoment_le D μ a Finset.univ p
      simp only [Finset.card_univ,Fintype.card_fin] at hb
      exact (mul_le_mul (scalarGamma_le_one β0 μ p p.property) hb (norm_nonneg _) zero_le_one).trans_eq (one_mul B))
  have hg : Integrable (fun p=>A p+6*J p) ν := hA.add (hJ.const_mul 6)
  have hb := norm_integral_le_of_norm_le hg (.of_forall fun p=>by
    have hp := cavitySignedResponseT3Diagonal_point_bound D μ a β0 hβ0 p
    rw [Real.norm_of_nonneg hp.1]
    exact hp.2)
  rw [integral_add hA (hJ.const_mul 6),integral_const_mul,Real.norm_eq_abs] at hb
  exact hb

end QuantitativeFollowup
