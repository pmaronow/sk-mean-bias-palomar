module
public import QuantitativeFollowup.FollowupCavitySignedResponseIntegratedPairing
public import QuantitativeFollowup.ScalarProcessContinuity

@[expose] public section

/-! Literal isolated-spin kernels and the corresponding native terminal
residual contributions. The scalar kernels are actual Gaussian expectations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1000000

def cavitySignedScalarKernelOne (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) : ℝ :=
  ∫ω,M β0 μ p ω*C β0 μ p ω*M β0 μ r ω ∂canonicalBrownianMeasure

def cavitySignedScalarKernelMarked (β0 : ℝ) (hβ0 : β0≠0) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) : ℝ :=
  ∫z,scalarCenteredSquare β0 μ p z.1*Paper.spinSign z.2*M β0 μ r z.1
    ∂scalarMarkedSpinLaw β0 hβ0 μ

private theorem norm_scalar_C_le_one (β0 : ℝ) (μ : Paper.ParisiMeasure) (p : Paper.Overlap)
    (ω : Paper.BrownianSample) : ‖C β0 μ p ω‖≤1 := by
  simp only [C,jetProcess,parisiSpatialJet_two]
  exact norm_parisiHessian_le_one_all _ _ _

theorem continuous_cavitySignedScalarKernelOne (β0 : ℝ) (hβ0 : β0≠0) (μ : Paper.ParisiMeasure) :
    Continuous (Function.uncurry (cavitySignedScalarKernelOne β0 μ)) := by
  apply continuous_of_dominated (μ := canonicalBrownianMeasure) (bound := fun _=>(1:ℝ))
  · intro z
    exact (((measurable_M β0 μ z.2 z.2.property).mul (measurable_C β0 hβ0 μ z.2.property)).mul
      (measurable_M β0 μ z.1 z.1.property)).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω=>by
      rw [norm_mul,norm_mul]
      exact (mul_le_mul (mul_le_mul (scalar_M_norm_le_one β0 μ z.2 ω)
        (norm_scalar_C_le_one β0 μ z.2 ω) (norm_nonneg _) zero_le_one)
        (scalar_M_norm_le_one β0 μ z.1 ω) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · exact integrable_const _
  · exact .of_forall fun ω=>by
      have hpm : Continuous (fun z : Paper.Overlap×Paper.Overlap => (μ,z.2)) :=
        continuous_const.prodMk continuous_snd
      have hrm : Continuous (fun z : Paper.Overlap×Paper.Overlap => (μ,z.1)) :=
        continuous_const.prodMk continuous_fst
      have hp := (continuous_scalarM_parameter β0 hβ0 ω).comp hpm
      have hc := (continuous_scalarC_parameter β0 hβ0 ω).comp hpm
      have hr := (continuous_scalarM_parameter β0 hβ0 ω).comp hrm
      exact (hp.mul hc).mul hr

theorem continuous_cavitySignedScalarKernelMarked (β0 : ℝ) (hβ0 : β0≠0) (μ : Paper.ParisiMeasure) :
    Continuous (Function.uncurry (cavitySignedScalarKernelMarked β0 hβ0 μ)) := by
  apply continuous_of_dominated (μ := scalarMarkedSpinLaw β0 hβ0 μ) (bound := fun _=>(1:ℝ))
  · intro z
    have hf : Measurable (scalarCenteredSquare β0 μ z.2) :=
      ((measurable_M β0 μ z.2 z.2.property).pow_const 2).sub measurable_const
    exact ((((hf.comp measurable_fst).mul ((measurable_of_finite Paper.spinSign).comp measurable_snd)).mul
      ((measurable_M β0 μ z.1 z.1.property).comp measurable_fst))).aestronglyMeasurable
  · intro z
    exact .of_forall fun p=>by
      rw [norm_mul,norm_mul]
      have hs : ‖Paper.spinSign p.2‖=1 := by simp only [Real.norm_eq_abs,Paper.abs_spinSign]
      rw [hs,mul_one]
      exact (mul_le_mul (scalarCenteredSquare_norm_le_one β0 μ z.2 p.1)
        (scalar_M_norm_le_one β0 μ z.1 p.1) (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  · exact integrable_const _
  · exact .of_forall fun p=>by
      have hpm : Continuous (fun z : Paper.Overlap×Paper.Overlap => (μ,z.2)) :=
        continuous_const.prodMk continuous_snd
      have hrm : Continuous (fun z : Paper.Overlap×Paper.Overlap => (μ,z.1)) :=
        continuous_const.prodMk continuous_fst
      have hp := (continuous_scalarCenteredSquare_parameter β0 hβ0 p.1).comp hpm
      have hr := (continuous_scalarM_parameter β0 hβ0 p.1).comp hrm
      exact (hp.mul continuous_const).mul hr

theorem cavitySignedScalarKernelOne_square_le (β0 : ℝ) (hβ0 : β0≠0)
    (μ : Paper.ParisiMeasure) (r p : Paper.Overlap) :
    (cavitySignedScalarKernelOne β0 μ r p)^2≤Gamma β0 μ r*Gamma β0 μ p := by
  have h := scalar_M_C_M_pairing β0 hβ0 μ p r p.property r.property
  have hs := Real.sq_sqrt (mul_nonneg (scalarGamma_nonneg β0 μ p) (scalarGamma_nonneg β0 μ r))
  change |cavitySignedScalarKernelOne β0 μ r p|≤_ at h
  have h2 := pow_le_pow_left₀ (abs_nonneg (cavitySignedScalarKernelOne β0 μ r p)) h 2
  rw [sq_abs,hs] at h2
  simpa only [mul_comm] using h2

theorem cavitySignedScalarKernelMarked_square_le (β0 : ℝ) (hβ0 : β0≠0)
    (μ : Paper.ParisiMeasure) (r p : Paper.Overlap) :
    (cavitySignedScalarKernelMarked β0 hβ0 μ r p)^2≤Gamma β0 μ r*Gamma β0 μ p := by
  have h := scalar_marked_centered_spin_pairing β0 hβ0 μ p r
  have hs := Real.sq_sqrt (mul_nonneg (scalarGamma_nonneg β0 μ p) (scalarGamma_nonneg β0 μ r))
  change |cavitySignedScalarKernelMarked β0 hβ0 μ r p|≤_ at h
  have h2 := pow_le_pow_left₀ (abs_nonneg (cavitySignedScalarKernelMarked β0 hβ0 μ r p)) h 2
  rw [sq_abs,hs] at h2
  simpa only [mul_comm] using h2

def cavitySignedScalarKernelOneFuture (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) : ℝ := if r<p then cavitySignedScalarKernelOne β0 μ r p else 0

theorem measurable_cavitySignedScalarKernelOneFuture (β0 : ℝ) (hβ0 : β0≠0) (μ : Paper.ParisiMeasure) :
    Measurable (Function.uncurry (cavitySignedScalarKernelOneFuture β0 μ)) :=
  (continuous_cavitySignedScalarKernelOne β0 hβ0 μ).measurable.ite
    (measurableSet_lt measurable_fst measurable_snd) measurable_const

theorem cavitySignedScalarKernelOneFuture_square_le (β0 : ℝ) (hβ0 : β0≠0)
    (μ : Paper.ParisiMeasure) (r p : Paper.Overlap) :
    (cavitySignedScalarKernelOneFuture β0 μ r p)^2≤Gamma β0 μ r*Gamma β0 μ p := by
  by_cases hrp : r<p
  · simpa only [cavitySignedScalarKernelOneFuture,if_pos hrp] using cavitySignedScalarKernelOne_square_le β0 hβ0 μ r p
  · simpa only [cavitySignedScalarKernelOneFuture,if_neg hrp,zero_pow (by decide : 2≠0)] using
      mul_nonneg (scalarGamma_nonneg β0 μ r) (scalarGamma_nonneg β0 μ p)

theorem cavitySignedResponse_T1_terminal_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (hn : 0<n) :
    |(-2:ℝ)*(∫r,∫p,cavitySignedResponseTerminalResidual D μ r p*
      anisotropicWeightedSelfOverlap D μ a (cavitySignedScalarKernelOneFuture β0 μ r) Finset.univ p.1
      ∂anisotropicMeasureSpinPathLaw D μ a ∂parisiFreeMeasure μ a)| ≤
      4*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  have h := cavitySignedResponse_integrated_terminal_pairing D μ a β0 hβ0 ha hμ hn
    (cavitySignedScalarKernelOneFuture β0 μ) (measurable_cavitySignedScalarKernelOneFuture β0 hβ0 μ)
    (cavitySignedScalarKernelOneFuture_square_le β0 hβ0 μ)
  rw [abs_mul]
  norm_num
  exact (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

theorem cavitySignedResponse_T2_terminal_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (hn : 0<n) :
    |∫r,∫p,cavitySignedResponseTerminalResidual D μ r p*
      anisotropicWeightedSelfOverlap D μ a (cavitySignedScalarKernelMarked β0 hβ0 μ r) Finset.univ p.1
      ∂anisotropicMeasureSpinPathLaw D μ a ∂parisiFreeMeasure μ a| ≤
      2*cavitySignedResponseWeightedJ D μ a β0 Finset.univ :=
  cavitySignedResponse_integrated_terminal_pairing D μ a β0 hβ0 ha hμ hn
    (cavitySignedScalarKernelMarked β0 hβ0 μ) (continuous_cavitySignedScalarKernelMarked β0 hβ0 μ).measurable
    (cavitySignedScalarKernelMarked_square_le β0 hβ0 μ)

end QuantitativeFollowup
