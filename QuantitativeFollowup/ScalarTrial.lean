module
public import QuantitativeFollowup.ScalarDensity
public import FRSB.CDFMeasureExt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

@[expose] public section

/-! Actual Stieltjes free measure of the clipped scalar trial profile.
Its initial value is kept separate as the prescribed atom at zero. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB
open scoped Topology
namespace QuantitativeFollowup

def scalarTrialStieltjes (β : ℝ) (hβ : 0 ≤ β) (lam : ℝ)
    (μ : Paper.ParisiMeasure) : StieltjesFunction ℝ where
  toFun := scalarTrialProfile β lam μ
  mono' := monotone_const.max ((parisiCDF_monotone μ).const_mul hβ)
  right_continuous' x := continuousWithinAt_const.max
    ((parisiCDF_right_continuous μ x).const_mul β)

@[simp] theorem scalarTrialStieltjes_apply (β : ℝ) (hβ : 0 ≤ β) (lam : ℝ)
    (μ : Paper.ParisiMeasure) (x : ℝ) :
    scalarTrialStieltjes β hβ lam μ x = scalarTrialProfile β lam μ x := rfl

theorem scalarTrialStieltjes_atBot (β : ℝ) (hβ : 0 ≤ β)
    (lam : ℝ) (hlam : 0 ≤ lam) (μ : Paper.ParisiMeasure) :
    Tendsto (scalarTrialStieltjes β hβ lam μ) atBot (𝓝 lam) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  simp only [scalarTrialStieltjes_apply,scalarTrialProfile,
    parisiCDF_eq_zero_of_lt_zero μ hx,mul_zero,max_eq_left hlam]

theorem scalarTrialStieltjes_atTop (β : ℝ) (hβ : 0 ≤ β)
    (lam : ℝ) (hlam : lam ≤ β) (μ : Paper.ParisiMeasure) :
    Tendsto (scalarTrialStieltjes β hβ lam μ) atTop (𝓝 β) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hCDF : parisiCDF μ x = 1 := parisiCDF_eq_one_above_support μ
    (fun z hz => by obtain ⟨w,hw,rfl⟩ := hz; exact w.property.2) hx
  simp only [scalarTrialStieltjes_apply,scalarTrialProfile,hCDF,mul_one,max_eq_right hlam]

theorem scalar_trial_free_mass (β : ℝ) (hβ : 0 ≤ β)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) β) (μ : Paper.ParisiMeasure) :
    (scalarTrialStieltjes β hβ lam μ).measure univ = ENNReal.ofReal (β-lam) :=
  StieltjesFunction.measure_univ _
    (scalarTrialStieltjes_atBot β hβ lam hlam.1 μ)
    (scalarTrialStieltjes_atTop β hβ lam hlam.2 μ)

theorem scalar_trial_free_measure_Ioc (β : ℝ) (hβ : 0 ≤ β)
    (lam : ℝ) (μ : Paper.ParisiMeasure) (x y : ℝ) :
    (scalarTrialStieltjes β hβ lam μ).measure (Ioc x y) =
      ENNReal.ofReal (scalarTrialProfile β lam μ y-scalarTrialProfile β lam μ x) :=
  StieltjesFunction.measure_Ioc _ x y

theorem scalar_trial_absolutelyContinuous_below_terminal (β : ℝ) (hβ : 0 < β)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ lam a b : ℝ, a ∈ Ico (0 : ℝ) q →
      b ∈ Ico (0 : ℝ) q →
      LipschitzOnWith (Real.toNNReal L) (scalarTrialProfile β lam μ) (uIcc a b) ∧
      AbsolutelyContinuousOnInterval (scalarTrialProfile β lam μ) a b := by
  obtain ⟨L,hL,hLip⟩ := scalar_trial_lipschitz_below_terminal β hβ μ hmin q hq hsupp
  refine ⟨L,hL,?_⟩
  intro lam a b ha hb
  have hsub : uIcc a b ⊆ Ico (0 : ℝ) q :=
    fun x hx => ⟨(le_min ha.1 hb.1).trans hx.1,
      hx.2.trans_lt (max_lt ha.2 hb.2)⟩
  have hK : LipschitzOnWith (Real.toNNReal L) (scalarTrialProfile β lam μ) (uIcc a b) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    simpa only [dist_eq_norm,Real.coe_toNNReal L (zero_le_one.trans hL)] using hLip lam y x (hsub hy) (hsub hx)
  exact ⟨hK,hK.absolutelyContinuousOnInterval⟩

theorem scalar_trial_density_Ioc (β : ℝ) (hβ : 0 < β)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q)
    (lam a b : ℝ) (ha : a ∈ Ico (0 : ℝ) q) (hb : b ∈ Ico (0 : ℝ) q) :
    (scalarTrialStieltjes β hβ.le lam μ).measure (Ioc a b) =
      ENNReal.ofReal (∫ x in a..b, deriv (scalarTrialProfile β lam μ) x) := by
  obtain ⟨L,hL,hac⟩ := scalar_trial_absolutelyContinuous_below_terminal
    β hβ μ hmin q hq hsupp
  rw [(hac lam a b ha hb).2.integral_deriv_eq_sub,scalar_trial_free_measure_Ioc]

theorem scalar_trial_density_bounded (β : ℝ) (hβ : 0 < β)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ lam x : ℝ, x ∈ Ioo (0 : ℝ) q →
      deriv (scalarTrialProfile β lam μ) x ∈ Icc (0 : ℝ) L := by
  obtain ⟨L,hL,hac⟩ := scalar_trial_absolutelyContinuous_below_terminal
    β hβ μ hmin q hq hsupp
  refine ⟨L,hL,?_⟩
  intro lam x hx
  let b := (x+q)/2
  have hb : b ∈ Ico (0 : ℝ) q := ⟨by dsimp [b]; linarith [hx.1,hx.2], by dsimp [b]; linarith [hx.1,hx.2]⟩
  have hxb : x < b := by dsimp [b]; linarith [hx.1,hx.2]
  have hK := (hac lam 0 b ⟨le_rfl,hq.1⟩ hb).1
  have hbound := norm_deriv_le_of_lipschitzOn
    (show uIcc (0 : ℝ) b ∈ 𝓝 x by
      rw [uIcc_of_le hb.1]; exact Icc_mem_nhds hx.1 hxb) hK
  have hn : 0 ≤ deriv (scalarTrialProfile β lam μ) x :=
    (scalarTrialStieltjes β hβ.le lam μ).mono.deriv_nonneg
  refine ⟨hn,?_⟩
  rw [Real.norm_eq_abs,abs_of_nonneg hn,Real.coe_toNNReal L (zero_le_one.trans hL)] at hbound
  exact hbound

end QuantitativeFollowup
