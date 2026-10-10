module
public import QuantitativeFollowup.ScalarKernelBasics
public import FourPapersCommon.L2CauchySchwarz

@[expose] public section

/-! Genuine scalar kernel product bounds. The bounded multiplier version
also records exactly the analytic input needed when a terminal spin is
adjoined to the diffusion law; no conditional spin law is assumed here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 800000

theorem scalar_M_norm_le_one (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ) (ω : Paper.BrownianSample) :
    ‖M β μ p ω‖≤1 := by
  simpa only [M,jetProcess,parisiSpatialJet_one] using
    norm_parisiGradient_le_one β μ (p,optimalStateReal β μ ω p)

theorem scalar_M_memLp_two (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ)
    (hp : p∈Icc (0:ℝ) 1) : MemLp (M β μ p) 2 canonicalBrownianMeasure :=
  MemLp.of_bound (measurable_M β μ p hp).aestronglyMeasurable 1
    (.of_forall fun ω=>scalar_M_norm_le_one β μ p ω)

def scalarCenteredSquare (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ) (ω : Paper.BrownianSample) : ℝ :=
  M β μ p ω^2-Gamma β μ p

theorem scalarCenteredSquare_memLp_two (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ)
    (hp : p∈Icc (0:ℝ) 1) : MemLp (scalarCenteredSquare β μ p) 2 canonicalBrownianMeasure := by
  have hf : MemLp (fun ω=>M β μ p ω^2) 2 canonicalBrownianMeasure:=
    MemLp.of_bound ((measurable_M β μ p hp).pow_const 2).aestronglyMeasurable 1
      (.of_forall fun ω=>by rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) (scalar_M_norm_le_one β μ p ω))
  exact hf.sub (memLp_const (Gamma β μ p))

theorem scalarCenteredSquare_secondMoment_le (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ)
    (hp : p∈Icc (0:ℝ) 1) :
    (∫ω,scalarCenteredSquare β μ p ω^2∂canonicalBrownianMeasure)≤Gamma β μ p := by
  have he : (∫ω,scalarCenteredSquare β μ p ω^2∂canonicalBrownianMeasure)=
      variance (fun ω=>M β μ p ω^2) canonicalBrownianMeasure := by
    rw [variance_eq_integral ((measurable_M β μ p hp).pow_const 2).aemeasurable]
    rfl
  rw [he]
  exact (scalar_square_variance_bound β μ p hp).2

theorem scalar_M_times_unit_secondMoment_le (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ)
    (hp : p∈Icc (0:ℝ) 1) (H : Paper.BrownianSample→ℝ) (hH : Measurable H)
    (hbH : ∀ω,‖H ω‖≤1) :
    MemLp (fun ω=>M β μ p ω*H ω) 2 canonicalBrownianMeasure ∧
      (∫ω,(M β μ p ω*H ω)^2∂canonicalBrownianMeasure)≤Gamma β μ p := by
  have hf : MemLp (fun ω=>M β μ p ω*H ω) 2 canonicalBrownianMeasure:=
    MemLp.of_bound ((measurable_M β μ p hp).mul hH).aestronglyMeasurable 1
      (.of_forall fun ω=>by
        rw [norm_mul]
        exact (mul_le_mul (scalar_M_norm_le_one β μ p ω) (hbH ω) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  refine ⟨hf,integral_mono hf.integrable_sq (integrable_M_sq β μ p hp) (fun ω=>?_ )⟩
  have hs : H ω^2≤1:=by
    simpa only [Real.norm_eq_abs,sq_abs] using pow_le_one₀ (n:=2) (norm_nonneg _) (hbH ω)
  rw [mul_pow]
  exact (mul_le_mul_of_nonneg_left hs (sq_nonneg _)).trans_eq (mul_one _)

theorem scalar_M_unit_M_pairing (β : ℝ) (μ : Paper.ParisiMeasure) (p r : ℝ)
    (hp : p∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) 1)
    (H : Paper.BrownianSample→ℝ) (hH : Measurable H) (hbH : ∀ω,‖H ω‖≤1) :
    |∫ω,M β μ p ω*H ω*M β μ r ω∂canonicalBrownianMeasure|≤
      Real.sqrt (Gamma β μ p*Gamma β μ r) := by
  have hf:=scalar_M_times_unit_secondMoment_le β μ p hp H hH hbH
  exact FourPapersCommon.integral_mul_abs_le_sqrt_moment_bounds _ _ hf.1
    (scalar_M_memLp_two β μ r hr) _ _ hf.2 le_rfl

theorem scalar_M_C_M_pairing (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (p r : ℝ)
    (hp : p∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) 1) :
    |∫ω,M β μ p ω*C β μ p ω*M β μ r ω∂canonicalBrownianMeasure|≤
      Real.sqrt (Gamma β μ p*Gamma β μ r) := by
  apply scalar_M_unit_M_pairing β μ p r hp hr _ (measurable_C β hβ μ hp)
  intro ω
  simp only [C,jetProcess,parisiSpatialJet_two]
  exact norm_parisiHessian_le_one_all _ _ _

theorem scalar_centered_square_unit_M_pairing (β : ℝ) (μ : Paper.ParisiMeasure) (p r : ℝ)
    (hp : p∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) 1)
    (H : Paper.BrownianSample→ℝ) (hH : Measurable H) (hbH : ∀ω,‖H ω‖≤1) :
    |∫ω,scalarCenteredSquare β μ p ω*H ω*M β μ r ω∂canonicalBrownianMeasure|≤
      Real.sqrt (Gamma β μ p*Gamma β μ r) := by
  have hf:=scalarCenteredSquare_memLp_two β μ p hp
  have hprod : MemLp (fun ω=>scalarCenteredSquare β μ p ω*H ω) 2 canonicalBrownianMeasure:=by
    apply hf.mono (hf.aestronglyMeasurable.mul hH.aestronglyMeasurable)
    filter_upwards with ω
    change ‖scalarCenteredSquare β μ p ω*H ω‖≤‖scalarCenteredSquare β μ p ω‖
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hbH ω) (norm_nonneg _)).trans_eq (mul_one _)
  have hmoment : (∫ω,(scalarCenteredSquare β μ p ω*H ω)^2∂canonicalBrownianMeasure)≤Gamma β μ p := by
    apply (integral_mono hprod.integrable_sq hf.integrable_sq (fun ω=>?_)).trans
      (scalarCenteredSquare_secondMoment_le β μ p hp)
    have hs : H ω^2≤1:=by
      simpa only [Real.norm_eq_abs,sq_abs] using (pow_le_one₀ (n:=2) (norm_nonneg _) (hbH ω))
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left hs (sq_nonneg _)).trans_eq (mul_one _)
  exact FourPapersCommon.integral_mul_abs_le_sqrt_moment_bounds _ _ hprod
    (scalar_M_memLp_two β μ r hr) _ _ hmoment le_rfl

theorem scalar_M_product_secondMoment_le (β : ℝ) (μ : Paper.ParisiMeasure) (r ell : ℝ)
    (hr : r∈Icc (0:ℝ) 1) (hell : ell∈Icc (0:ℝ) 1) :
    MemLp (fun ω=>M β μ r ω*M β μ ell ω) 2 canonicalBrownianMeasure ∧
      (∫ω,(M β μ r ω*M β μ ell ω)^2∂canonicalBrownianMeasure)≤Gamma β μ (min r ell) := by
  have hf:=scalar_M_times_unit_secondMoment_le β μ r hr (M β μ ell) (measurable_M β μ ell hell)
    (scalar_M_norm_le_one β μ ell)
  refine ⟨hf.1,?_⟩
  by_cases h : r≤ell
  · simpa only [min_eq_left h] using hf.2
  · have hg:=scalar_M_times_unit_secondMoment_le β μ ell hell (M β μ r) (measurable_M β μ r hr)
      (scalar_M_norm_le_one β μ r)
    simpa only [min_eq_right (lt_of_not_ge h).le,mul_comm] using hg.2

theorem scalar_centered_square_M_M_pairing (β : ℝ) (μ : Paper.ParisiMeasure) (p r ell : ℝ)
    (hp : p∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) 1) (hell : ell∈Icc (0:ℝ) 1) :
    |∫ω,scalarCenteredSquare β μ p ω*M β μ r ω*M β μ ell ω∂canonicalBrownianMeasure|≤
      Real.sqrt (Gamma β μ p*Gamma β μ (min r ell)) := by
  have hg:=scalar_M_product_secondMoment_le β μ r ell hr hell
  have hh:=FourPapersCommon.integral_mul_abs_le_sqrt_moment_bounds _ _
    (scalarCenteredSquare_memLp_two β μ p hp) hg.1 _ _
    (scalarCenteredSquare_secondMoment_le β μ p hp) hg.2
  simpa only [mul_assoc] using hh

end QuantitativeFollowup
