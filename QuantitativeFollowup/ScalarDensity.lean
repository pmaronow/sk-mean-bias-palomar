module
public import FRSB.FullSupport
public import FRSB.SupportMomentSmooth
public import FRSB.ParisiStrictConvexity
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! The actual scalar density bound in Lemma 5.4 of the quantitative
follow-up. The smooth CDF extension and the terminal support geometry are
already kernel-checked in the FRSB foundation; no density or moment
regularity is supplied as an extra hypothesis. -/
noncomputable section
open Set MeasureTheory Paper FRSB
open scoped ContDiff
namespace QuantitativeFollowup

theorem scalar_cdf_lipschitz_below_terminal (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Ico (0 : ℝ) q, ∀ y ∈ Ico (0 : ℝ) q,
      ‖parisiCDF μ y - parisiCDF μ x‖ ≤ L * ‖y - x‖ := by
  have hF := (moments_contDiffOn_on_support_interval β hβ μ hmin q hq.1
    hq.2.le hsupp).2
  have hρ := (parisiSmoothDensity_regular_of_support_interval β hβ μ hmin q
    hq.1 hq.2.le hsupp).1.continuousOn
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := q)).exists_bound_of_continuousOn hρ
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 ⟨le_rfl, hq.1.le⟩)
  refine ⟨L, hL0, ?_⟩
  intro x hx y hy
  rw [parisiCDF_eq_momentQuotient_on_support_interval β hβ μ hmin q hq.1
      hq.2.le hsupp y hy,
    parisiCDF_eq_momentQuotient_on_support_interval β hβ μ hmin q hq.1
      hq.2.le hsupp x hx]
  apply Convex.norm_image_sub_le_of_norm_derivWithin_le
    (hF.differentiableOn (by simp)) _ (convex_Icc (0 : ℝ) q)
    ⟨hx.1, hx.2.le⟩ ⟨hy.1, hy.2.le⟩
  intro z hz
  exact hL z hz

theorem scalar_cdf_increment_bound (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, 0 ≤ x → x < y → y < q →
      parisiCDF μ y - parisiCDF μ x ≤ L * (y - x) := by
  obtain ⟨L, hL0, hL⟩ := scalar_cdf_lipschitz_below_terminal β hβ μ hmin q hq hsupp
  refine ⟨L, hL0, ?_⟩
  intro x y hx hxy hy
  have hb := hL x ⟨hx, hxy.trans hy⟩ y ⟨hx.trans hxy.le, hy⟩
  simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy.le)] at hb
  exact (le_abs_self _).trans hb

/-- The paper's scalar measure has actual interval support and a finite
Lipschitz bound, derived for every minimizing measure. -/
theorem scalar_minimizer_density_bound (β : ℝ) (hβ : 1 < β)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ) :
    ∃ q : ℝ, q ∈ Ioo (0 : ℝ) 1 ∧ parisiSupport μ = Icc (0 : ℝ) q ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, 0 ≤ x → x < y → y < q →
        parisiCDF μ y - parisiCDF μ x ≤ L * (y - x) := by
  obtain ⟨q, hq, hsupp⟩ := minimizer_full_support β hβ μ hmin
  exact ⟨q, hq, hsupp, scalar_cdf_increment_bound β (zero_lt_one.trans hβ).ne'
    μ hmin q hq hsupp⟩

/-- Constants and terminal overlap depend only on the fixed temperature,
and work simultaneously for every actual minimizing measure. -/
theorem scalar_density_bound_uniform_minimizers (β : ℝ) (hβ : 1 < β) :
    ∃ q : ℝ, q ∈ Ioo (0 : ℝ) 1 ∧ ∃ L : ℝ, 0 ≤ L ∧
      ∀ μ : Paper.ParisiMeasure, IsParisiMinimizer β 0 μ →
        parisiSupport μ = Icc (0 : ℝ) q ∧
        ∀ x y : ℝ, 0 ≤ x → x < y → y < q →
          parisiCDF μ y - parisiCDF μ x ≤ L * (y - x) := by
  obtain ⟨q, hq, hsupp, L, hL0, hL⟩ := scalar_minimizer_density_bound β hβ
    (parisiMinimizer β 0) (isParisiMinimizer_selected β 0)
  refine ⟨q, hq, L, hL0, ?_⟩
  intro μ hμ
  rw [parisiMinimizer_unique β (zero_lt_one.trans hβ).ne' μ hμ]
  exact ⟨hsupp, hL⟩

def scalarTrialProfile (β lam : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) : ℝ :=
  max lam (β*parisiCDF μ q)

theorem scalar_trial_lipschitz_below_terminal (β : ℝ) (hβ : 0 < β)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ lam x y : ℝ, x ∈ Ico (0 : ℝ) q → y ∈ Ico (0 : ℝ) q →
      ‖scalarTrialProfile β lam μ y-scalarTrialProfile β lam μ x‖ ≤ L*‖y-x‖ := by
  obtain ⟨L, hL0, hL⟩ := scalar_cdf_lipschitz_below_terminal β hβ.ne' μ hmin q hq hsupp
  refine ⟨max 1 (β*L), le_max_left _ _, ?_⟩
  intro lam x y hx hy
  have hm := abs_max_sub_max_le_abs (β*parisiCDF μ y) (β*parisiCDF μ x) lam
  simp only [scalarTrialProfile, max_comm lam, Real.norm_eq_abs] at hm ⊢
  have hb := hL x hx y hy
  simp only [Real.norm_eq_abs] at hb
  calc
    _ ≤ |β*parisiCDF μ y-β*parisiCDF μ x| := hm
    _ = β*|parisiCDF μ y-parisiCDF μ x| := by
      rw [←mul_sub,abs_mul,abs_of_pos hβ]
    _ ≤ (β*L)*|y-x| := by nlinarith
    _ ≤ max 1 (β*L)*|y-x| := mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)

theorem scalar_trial_initial (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q)
    (lam : ℝ) (hlam : 0 ≤ lam) : scalarTrialProfile β lam μ 0 = lam := by
  rw [scalarTrialProfile, parisiCDF_eq_momentQuotient_on_support_interval
    β hβ μ hmin q hq.1 hq.2.le hsupp 0 ⟨le_rfl,hq.1⟩,
    momentQuotient_initial_zero, mul_zero, max_eq_left hlam]

theorem scalar_trial_terminal (β lam : ℝ) (μ : Paper.ParisiMeasure)
    (q : ℝ) (hsupp : parisiSupport μ = Icc (0 : ℝ) q)
    (hlam : lam ≤ β) (x : ℝ) (hx : q ≤ x) :
    scalarTrialProfile β lam μ x = β := by
  rw [scalarTrialProfile, parisiCDF_eq_one_above_support μ
    (fun z hz => (hsupp ▸ hz).2) hx, mul_one, max_eq_right hlam]

end QuantitativeFollowup
