module
public import QuantitativeFollowup.ScalarTrialMeasure
public import QuantitativeFollowup.StieltjesLipschitz

@[expose] public section

/-! Actual domination of the clipped trial's free measure below its
terminal atom. Clipping removes mass from the free measure; this is proved
by decomposing the original CDF into its maximum and minimum truncations. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB
open scoped Topology ENNReal NNReal
namespace QuantitativeFollowup

theorem scalar_trial_free_measure_le (β : ℝ) (hβ : 0 ≤ β)
    (lam : ℝ) (μ : Paper.ParisiMeasure) :
    (scalarTrialStieltjes β hβ lam μ).measure ≤
      ENNReal.ofReal β • (μ : Measure Paper.Overlap).map Subtype.val := by
  let c : ℝ≥0 := ⟨β,hβ⟩
  let f := c • cdf ((μ : Measure Paper.Overlap).map Subtype.val)
  have he : stieltjesMax f lam = scalarTrialStieltjes β hβ lam μ := by
    ext x
    change max lam (β * cdf ((μ : Measure Paper.Overlap).map Subtype.val) x) =
      max lam (β*parisiCDF μ x)
    rw [parisiCDF_eq_realCDF]
  have hm := stieltjesMax_measure_le f lam
  rw [he] at hm
  have hs : f.measure = ENNReal.ofReal β •
      (μ : Measure Paper.Overlap).map Subtype.val := by
    rw [StieltjesFunction.measure_smul,measure_cdf]
    ext S
    change (c : ℝ≥0∞)*((μ : Measure Paper.Overlap).map Subtype.val) S =
      ENNReal.ofReal β*((μ : Measure Paper.Overlap).map Subtype.val) S
    rw [←ENNReal.ofReal_coe_nnreal (p := c)]
    rfl
  rwa [hs] at hm

theorem scalar_trial_density_domination (β : ℝ) (hβ : 0 < β)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ lam : ℝ,
      (scalarTrialStieltjes β hβ.le lam μ).measure.restrict (Iio q) ≤
        ENNReal.ofReal L • volume.restrict (Ico (0 : ℝ) q) := by
  have hρ := (parisiSmoothDensity_regular_of_support_interval β hβ.ne' μ hmin q
    hq.1 hq.2.le hsupp).1.continuousOn
  obtain ⟨K,hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := q)).exists_bound_of_continuousOn hρ
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl,hq.1.le⟩)
  have hreal := parisiMeasure_eq_density_add_atom_of_support_interval
    β hβ.ne' μ hmin q hq.1 hq.2.le hsupp
  have hr : ((μ : Measure Paper.Overlap).map Subtype.val).restrict (Iio q) =
      (volume.restrict (Ico (0 : ℝ) q)).withDensity
        (fun x => ENNReal.ofReal (parisiSmoothDensity β μ q x)) := by
    rw [hreal,Measure.restrict_add,Measure.restrict_smul,
      restrict_dirac' measurableSet_Iio,
      if_neg (by simp : q ∉ Iio q),smul_zero,add_zero,
      restrict_withDensity measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
    rw [inter_eq_right.mpr (show Ico (0 : ℝ) q ⊆ Iio q from fun x hx => hx.2)]
  have hd : ((μ : Measure Paper.Overlap).map Subtype.val).restrict (Iio q) ≤
      ENNReal.ofReal K • volume.restrict (Ico (0 : ℝ) q) := by
    rw [hr,←withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using hK x ⟨hx.1,hx.2.le⟩))
  refine ⟨max 1 (β*K),le_max_left _ _,?_⟩
  intro lam
  calc
    _ ≤ (ENNReal.ofReal β • (μ : Measure Paper.Overlap).map Subtype.val).restrict (Iio q) :=
      Measure.restrict_mono_measure (scalar_trial_free_measure_le β hβ.le lam μ) _
    _ = ENNReal.ofReal β • ((μ : Measure Paper.Overlap).map Subtype.val).restrict (Iio q) :=
      Measure.restrict_smul _ _ _
    _ ≤ ENNReal.ofReal β • (ENNReal.ofReal K • volume.restrict (Ico (0 : ℝ) q)) := by
      intro S
      change ENNReal.ofReal β * _ ≤ ENNReal.ofReal β * _
      gcongr
      exact hd
    _ = ENNReal.ofReal (β*K) • volume.restrict (Ico (0 : ℝ) q) := by
      rw [smul_smul,ENNReal.ofReal_mul hβ.le]
    _ ≤ _ := by
      intro S
      change ENNReal.ofReal (β*K) * _ ≤ ENNReal.ofReal (max 1 (β*K)) * _
      gcongr
      exact le_max_right _ _

/-- Literal scalar trial density statement: a temperature-dependent bound
works for every actual scalar minimizer and every floor in [0,β]. The
terminal atom is retained, while the entire free measure below it is
dominated by bounded Lebesgue density. -/
theorem scalar_trial_density_bound_uniform_minimizers (β : ℝ) (hβ : 1 < β) :
    ∃ q : ℝ, q ∈ Ioo (0 : ℝ) 1 ∧ ∃ L : ℝ, 1 ≤ L ∧
      ∀ μ : Paper.ParisiMeasure, IsParisiMinimizer β 0 μ →
        parisiSupport μ = Icc (0 : ℝ) q ∧
        ∀ lam : ℝ, lam ∈ Icc (0 : ℝ) β →
          scalarTrialProfile β lam μ 0 = lam ∧
          (∀ x : ℝ, q ≤ x → scalarTrialProfile β lam μ x = β) ∧
          (∀ x y : ℝ, x ∈ Ico (0 : ℝ) q → y ∈ Ico (0 : ℝ) q →
            ‖scalarTrialProfile β lam μ y-scalarTrialProfile β lam μ x‖ ≤ L*‖y-x‖) ∧
          (scalarTrialStieltjes β (zero_le_one.trans hβ.le) lam μ).measure.restrict (Iio q) ≤
            ENNReal.ofReal L • volume.restrict (Ico (0 : ℝ) q) := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  let μ₀ := parisiMinimizer β 0
  have hm₀ : IsParisiMinimizer β 0 μ₀ := isParisiMinimizer_selected β 0
  obtain ⟨q,hq,hsupp⟩ := minimizer_full_support β hβ μ₀ hm₀
  obtain ⟨A,hA,hLip⟩ := scalar_trial_lipschitz_below_terminal β hβ0 μ₀ hm₀ q hq hsupp
  obtain ⟨B,hB,hDom⟩ := scalar_trial_density_domination β hβ0 μ₀ hm₀ q hq hsupp
  refine ⟨q,hq,max A B,hA.trans (le_max_left _ _),?_⟩
  intro μ hm
  have he : μ = μ₀ := parisiMinimizer_unique β hβ0.ne' μ hm
  subst μ
  refine ⟨hsupp,?_⟩
  intro lam hlam
  refine ⟨scalar_trial_initial β hβ0.ne' μ₀ hm₀ q hq hsupp lam hlam.1,
    scalar_trial_terminal β lam μ₀ q hsupp hlam.2,?_,?_⟩
  · intro x y hx hy
    exact (hLip lam x y hx hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · apply (hDom lam).trans
    intro S
    change ENNReal.ofReal B * _ ≤ ENNReal.ofReal (max A B) * _
    gcongr
    exact le_max_right _ _

/-- Constancy of the actual trial profile gives zero free mass strictly above
the terminal point, including the paper's interval `(q,1]`. -/
theorem scalar_trial_free_measure_above_terminal (β : ℝ) (hβ : 0 ≤ β)
    (lam : ℝ) (hlam : lam ≤ β) (μ : Paper.ParisiMeasure) (q : ℝ)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    (scalarTrialStieltjes β hβ lam μ).measure (Ioi q) = 0 ∧
      (scalarTrialStieltjes β hβ lam μ).measure (Ioc q 1) = 0 := by
  have hz : (scalarTrialStieltjes β hβ lam μ).measure (Ioi q) = 0 := by
    rw [StieltjesFunction.measure_Ioi _ (scalarTrialStieltjes_atTop β hβ lam hlam μ),
      scalarTrialStieltjes_apply,scalar_trial_terminal β lam μ q hsupp hlam q le_rfl]
    simp
  refine ⟨hz,measure_mono_null (fun x hx => hx.1) hz⟩

/-- The terminal point is the only possible singular part of the clipped
trial's free measure. This states absolute continuity of the full real-line
restriction, rather than only of compact subintervals below the terminal. -/
theorem scalar_trial_free_measure_absolutelyContinuous_away_terminal
    (β : ℝ) (hβ : 0 < β) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q)
    (lam : ℝ) (hlam : lam ≤ β) :
    (scalarTrialStieltjes β hβ.le lam μ).measure.restrict ({q}ᶜ) ≪ volume := by
  obtain ⟨L,hL,hDom⟩ := scalar_trial_density_domination β hβ μ hmin q hq hsupp
  have hz := (scalar_trial_free_measure_above_terminal β hβ.le lam hlam μ q hsupp).1
  have he : ({q}ᶜ : Set ℝ) = Iio q ∪ Ioi q := by
    ext x
    simp only [mem_compl_iff,mem_singleton_iff,mem_union,mem_Iio,mem_Ioi]
    exact ne_iff_lt_or_gt
  rw [he,Measure.restrict_union (by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact (lt_asymm (show x < q from hx) (show q < x from hy))) measurableSet_Ioi,
    Measure.restrict_eq_zero.mpr hz,add_zero]
  exact (Measure.absolutelyContinuous_of_le_smul (hDom lam)).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

end QuantitativeFollowup
