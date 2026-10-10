module
public import QuantitativeFollowup.FollowupCavitySignedResponseScalarKernels
public import QuantitativeFollowup.FollowupCavitySignedResponseDoublePairing

@[expose] public section

/-! The literal three-level isolated-spin kernel in T2 and its actual
symmetric-residual contribution, with the source coefficient one half. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000

def cavitySignedScalarKernelTriple (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (z : Paper.Overlap×Paper.Overlap) (p : Paper.Overlap) : ℝ :=
  ∫ω,scalarCenteredSquare β0 μ p ω*M β0 μ z.1 ω*M β0 μ z.2 ω ∂canonicalBrownianMeasure

theorem continuous_cavitySignedScalarKernelTriple (β0 : ℝ) (hβ0 : β0≠0) (μ : Paper.ParisiMeasure) :
    Continuous (Function.uncurry (cavitySignedScalarKernelTriple β0 μ)) := by
  apply continuous_of_dominated (μ := canonicalBrownianMeasure) (bound := fun _=>(1:ℝ))
  · intro z
    have hf : Measurable (scalarCenteredSquare β0 μ z.2) :=
      ((measurable_M β0 μ z.2 z.2.property).pow_const 2).sub measurable_const
    exact ((hf.mul (measurable_M β0 μ z.1.1 z.1.1.property)).mul
      (measurable_M β0 μ z.1.2 z.1.2.property)).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω=>by
      rw [norm_mul,norm_mul]
      exact (mul_le_mul (mul_le_mul (scalarCenteredSquare_norm_le_one β0 μ z.2 ω)
        (scalar_M_norm_le_one β0 μ z.1.1 ω) (norm_nonneg _) zero_le_one)
        (scalar_M_norm_le_one β0 μ z.1.2 ω) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · exact integrable_const _
  · exact .of_forall fun ω=>by
      have hpmap : Continuous (fun z : (Paper.Overlap×Paper.Overlap)×Paper.Overlap =>(μ,z.2)) :=
        continuous_const.prodMk continuous_snd
      have hrmap : Continuous (fun z : (Paper.Overlap×Paper.Overlap)×Paper.Overlap =>(μ,z.1.1)) :=
        continuous_const.prodMk continuous_fst.fst
      have hlmap : Continuous (fun z : (Paper.Overlap×Paper.Overlap)×Paper.Overlap =>(μ,z.1.2)) :=
        continuous_const.prodMk continuous_fst.snd
      have hp := (continuous_scalarCenteredSquare_parameter β0 hβ0 ω).comp hpmap
      have hr := (continuous_scalarM_parameter β0 hβ0 ω).comp hrmap
      have hl := (continuous_scalarM_parameter β0 hβ0 ω).comp hlmap
      have h := (hp.mul hr).mul hl
      exact h.congr (fun z=>rfl)

theorem cavitySignedScalarKernelTriple_square_le (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (r l p : Paper.Overlap) :
    (cavitySignedScalarKernelTriple β0 μ (r,l) p)^2≤Gamma β0 μ (min r l)*Gamma β0 μ p := by
  have h := scalar_centered_square_M_M_pairing β0 μ p r l p.property r.property l.property
  change |cavitySignedScalarKernelTriple β0 μ (r,l) p|≤_ at h
  have h2 := pow_le_pow_left₀ (abs_nonneg (cavitySignedScalarKernelTriple β0 μ (r,l) p)) h 2
  rw [sq_abs,Real.sq_sqrt (mul_nonneg (scalarGamma_nonneg β0 μ p)
    (scalarGamma_nonneg β0 μ (min (r:ℝ) l)))] at h2
  simpa only [mul_comm] using h2

theorem cavitySignedResponse_T2_double_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (hn : 0<n) :
    |(1/2:ℝ)*(∫r,∫l,∫sample,cavitySignedResponseSymmetricMeanResidual D μ r l sample*
      anisotropicWeightedSelfOverlap D μ a (cavitySignedScalarKernelTriple β0 μ (r,l)) Finset.univ sample
      ∂anisotropicMeasureSampleLaw D μ a ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)|≤
      2*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  have h := cavitySignedResponse_double_mean_residual_integral_bound D μ a β0 hβ0 ha hμ hn
    (cavitySignedScalarKernelTriple β0 μ) (continuous_cavitySignedScalarKernelTriple β0 hβ0 μ).measurable
      (cavitySignedScalarKernelTriple_square_le β0 μ)
  rw [abs_mul]
  norm_num
  exact (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤1/2)).trans_eq (by ring)

end QuantitativeFollowup
