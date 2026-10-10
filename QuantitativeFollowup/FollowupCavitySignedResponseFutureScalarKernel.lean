module
public import QuantitativeFollowup.FollowupCavitySignedResponseScalarKernels
public import QuantitativeFollowup.ScalarSpinConditional

@[expose] public section

/-! The genuine scalar future covariance kernel, represented by the two
observed centered squares. The whole-past restart identity proves the
representation; the covariance bound is not a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000

def cavitySignedScalarFutureCovarianceKernel (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (p l : Paper.Overlap) : ℝ :=
  ∫ω,scalarCenteredSquare β0 μ p ω*scalarCenteredSquare β0 μ l ω ∂canonicalBrownianMeasure

theorem continuous_cavitySignedScalarFutureCovarianceKernel (β0 : ℝ) (hβ0 : β0≠0) (μ : Paper.ParisiMeasure) :
    Continuous (Function.uncurry (cavitySignedScalarFutureCovarianceKernel β0 μ)) := by
  apply continuous_of_dominated (μ := canonicalBrownianMeasure) (bound := fun _=>(1:ℝ))
  · intro z
    have hp : Measurable (scalarCenteredSquare β0 μ z.1) :=
      ((measurable_M β0 μ z.1 z.1.property).pow_const 2).sub measurable_const
    have hl : Measurable (scalarCenteredSquare β0 μ z.2) :=
      ((measurable_M β0 μ z.2 z.2.property).pow_const 2).sub measurable_const
    exact (hp.mul hl).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω=>(norm_mul _ _).trans_le ((mul_le_mul
      (scalarCenteredSquare_norm_le_one β0 μ z.1 ω) (scalarCenteredSquare_norm_le_one β0 μ z.2 ω)
      (norm_nonneg _) zero_le_one).trans_eq (by norm_num))
  · exact integrable_const _
  · exact .of_forall fun ω=>by
      have hpmap : Continuous (fun z : Paper.Overlap×Paper.Overlap =>(μ,z.1)) := continuous_const.prodMk continuous_fst
      have hlmap : Continuous (fun z : Paper.Overlap×Paper.Overlap =>(μ,z.2)) := continuous_const.prodMk continuous_snd
      have hp := (continuous_scalarCenteredSquare_parameter β0 hβ0 ω).comp hpmap
      have hl := (continuous_scalarCenteredSquare_parameter β0 hβ0 ω).comp hlmap
      exact (hp.mul hl).congr (fun z=>rfl)

theorem cavitySignedScalarFutureCovarianceKernel_square_le (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (p l : Paper.Overlap) :
    (cavitySignedScalarFutureCovarianceKernel β0 μ p l)^2≤Gamma β0 μ p*Gamma β0 μ l := by
  have h := integral_mul_abs_le_sqrt_moment_bounds _ _
    (scalarCenteredSquare_memLp_two β0 μ p p.property) (scalarCenteredSquare_memLp_two β0 μ l l.property)
    _ _ (scalarCenteredSquare_secondMoment_le β0 μ p p.property) (scalarCenteredSquare_secondMoment_le β0 μ l l.property)
  change |cavitySignedScalarFutureCovarianceKernel β0 μ p l|≤_ at h
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rwa [sq_abs,Real.sq_sqrt (mul_nonneg (scalarGamma_nonneg β0 μ p) (scalarGamma_nonneg β0 μ l))] at h2

theorem cavitySignedScalarFutureCovarianceKernel_eq_actual_future (β0 : ℝ) (hβ0 : β0≠0)
    (μ : Paper.ParisiMeasure) (p l : Paper.Overlap) (hpl : (p:ℝ)≤l) :
    cavitySignedScalarFutureCovarianceKernel β0 μ p l=
      covariance (fun ω=>M β0 μ p ω^2) (scalarFutureSquareProcess β0 μ p l hpl) canonicalBrownianMeasure := by
  let Z := scalarCenteredSquare β0 μ p
  let F := fun ω : Paper.BrownianSample=>M β0 μ l ω^2
  let G := scalarFutureSquareProcess β0 μ p l hpl
  have hZ : Measurable[canonicalBrownianFiltration (p:ℝ).toNNReal] Z :=
    ((measurable_scalarM_past β0 hβ0 μ p).pow_const 2).sub measurable_const
  have hZi : MemLp Z 2 canonicalBrownianMeasure := scalarCenteredSquare_memLp_two β0 μ p p.property
  have hFi : MemLp F 2 canonicalBrownianMeasure := MemLp.of_bound
    ((measurable_M β0 μ l l.property).pow_const 2).aestronglyMeasurable 1
      (.of_forall fun ω=>by rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) (scalar_M_norm_le_one β0 μ l ω))
  have hGi := scalarFutureSquareProcess_memLp_two β0 hβ0 μ p l hpl
  have hZ0 : (∫ω,Z ω ∂canonicalBrownianMeasure)=0 := by
    rw [show Z=fun ω=>M β0 μ p ω^2-Gamma β0 μ p from rfl,
      integral_sub (integrable_M_sq β0 μ p p.property) (integrable_const _)]
    simp only [Gamma,integral_const,probReal_univ,one_smul,sub_self]
  have he := scalarFutureSquare_weighted_expectation β0 hβ0 μ p l hpl Z hZ 1
    (scalarCenteredSquare_norm_le_one β0 μ p)
  have hF (W : Paper.BrownianSample→ℝ) (hW : MemLp W 2 canonicalBrownianMeasure) :
      (∫ω,Z ω*(W ω-Gamma β0 μ l) ∂canonicalBrownianMeasure)=∫ω,Z ω*W ω ∂canonicalBrownianMeasure := by
    simp_rw [mul_sub]
    have hi1 : Integrable (fun ω=>Z ω*W ω) canonicalBrownianMeasure := hZi.integrable_mul hW
    have hi2 : Integrable (fun ω=>Z ω*Gamma β0 μ l) canonicalBrownianMeasure :=
      (hZi.integrable (by norm_num)).mul_const _
    rw [integral_sub hi1 hi2,integral_mul_const,hZ0,zero_mul,sub_zero]
  change (∫ω,Z ω*(F ω-Gamma β0 μ l) ∂canonicalBrownianMeasure)=_
  rw [hF F hFi,he]
  unfold covariance
  rw [integral_scalarFutureSquareProcess β0 hβ0 μ p l hpl]
  change (∫ω,Z ω*G ω ∂canonicalBrownianMeasure)=∫ω,Z ω*(G ω-Gamma β0 μ l) ∂canonicalBrownianMeasure
  exact (hF G hGi).symm

def cavitySignedScalarStrictFutureKernel (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (p l : Paper.Overlap) : ℝ := if p<l then cavitySignedScalarFutureCovarianceKernel β0 μ p l else 0

theorem measurable_cavitySignedScalarStrictFutureKernel (β0 : ℝ) (hβ0 : β0≠0) (μ : Paper.ParisiMeasure) :
    Measurable (Function.uncurry (cavitySignedScalarStrictFutureKernel β0 μ)) :=
  (continuous_cavitySignedScalarFutureCovarianceKernel β0 hβ0 μ).measurable.ite
    (measurableSet_lt measurable_fst measurable_snd) measurable_const

theorem cavitySignedScalarStrictFutureKernel_square_le (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (p l : Paper.Overlap) :
    (cavitySignedScalarStrictFutureKernel β0 μ p l)^2≤Gamma β0 μ p*Gamma β0 μ l := by
  by_cases h : p<l
  · simpa only [cavitySignedScalarStrictFutureKernel,if_pos h] using cavitySignedScalarFutureCovarianceKernel_square_le β0 μ p l
  · simpa only [cavitySignedScalarStrictFutureKernel,if_neg h,zero_pow (by decide : 2≠0)] using
      mul_nonneg (scalarGamma_nonneg β0 μ p) (scalarGamma_nonneg β0 μ l)

end QuantitativeFollowup
