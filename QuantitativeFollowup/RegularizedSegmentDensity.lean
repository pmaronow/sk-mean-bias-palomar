module
public import QuantitativeFollowup.RegularizedTrialGeometry

@[expose] public section

/-! The actual Stieltjes measure of the smoothed-to-trial segment has
bounded density away from the retained scalar terminal atom. The initial
atom does not appear in the free profile's derivative measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB QuantitativePaper
open scoped ENNReal NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1500000

theorem scalarTrialStieltjes_leftLim_zero_general (β lam : ℝ) (hβ : 0 ≤ β)
    (hlam : 0 ≤ lam) (μ : Paper.ParisiMeasure) :
    Function.leftLim (scalarTrialStieltjes β hβ lam μ) 0 = lam := by
  apply tendsto_nhds_unique ((scalarTrialStieltjes β hβ lam μ).mono.tendsto_leftLim 0)
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [mem_Iio] at hx
  simp [scalarTrialStieltjes_apply, scalarTrialProfile,
    parisiCDF_eq_zero_of_lt_zero μ hx, max_eq_left hlam]

theorem scalarTrialStieltjes_measure_zero (β lam : ℝ) (hβ : 0 ≤ β)
    (hlam : 0 ≤ lam) (μ : Paper.ParisiMeasure) (hroot : β * parisiCDF μ 0 = lam) :
    (scalarTrialStieltjes β hβ lam μ).measure {0} = 0 := by
  rw [StieltjesFunction.measure_singleton, scalarTrialStieltjes_leftLim_zero_general β lam hβ hlam μ,
    scalarTrialStieltjes_apply, scalarTrialProfile, hroot, max_self, sub_self, ENNReal.ofReal_zero]

theorem reflected_trial_stieltjes_density_le (β lam : ℝ) (hβ : 0 ≤ β)
    (μ : Paper.ParisiMeasure) (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) (1 / 2)) (hroot : β * s = lam) :
    (scalarTrialStieltjes β hβ lam (reflectedParisiMeasure μ s h hs hh.1)).measure ≤
      ENNReal.ofReal (β / h) • volume := by
  let ν := reflectedParisiMeasure μ s h hs hh.1
  let P := (scalarTrialStieltjes β hβ lam ν).measure
  have hlam : 0 ≤ lam := hroot ▸ mul_nonneg hβ hs.1
  have hz : P {0} = 0 := scalarTrialStieltjes_measure_zero β lam hβ hlam ν
    ((reflected_energy_root β μ s h hs hh).trans hroot)
  have hP : P = P.restrict ({0}ᶜ) := by
    have hd := Measure.restrict_compl_add_restrict (μ := P) (measurableSet_singleton (0 : ℝ))
    rw [Measure.restrict_eq_zero.mpr hz, add_zero] at hd
    exact hd.symm
  have hmap : (ν : Measure Paper.Overlap).map Subtype.val =
      ENNReal.ofReal s • Measure.dirac (0 : ℝ) +
        (parisiFreeMeasure ν s).map Subtype.val := by
    rw [← root_add_parisiFreeMeasure ν s hs (reflectedParisiMeasure_mem_floor μ s h hs hh),
      Measure.map_add _ _ measurable_subtype_coe,
      Measure.map_smul _ measurable_subtype_coe.aemeasurable,
      Measure.map_dirac zeroOverlap]
    rfl
  calc
    P = P.restrict ({0}ᶜ) := hP
    _ ≤ (ENNReal.ofReal β • (ν : Measure Paper.Overlap).map Subtype.val).restrict ({0}ᶜ) :=
      Measure.restrict_mono_measure (scalar_trial_free_measure_le β hβ lam ν) _
    _ = (ENNReal.ofReal β • (parisiFreeMeasure ν s).map Subtype.val).restrict ({0}ᶜ) := by
      rw [hmap, smul_add, Measure.restrict_add, smul_smul,
        Measure.restrict_smul, restrict_dirac' (measurableSet_singleton (0 : ℝ)).compl]
      simp
    _ ≤ ENNReal.ofReal β • (parisiFreeMeasure ν s).map Subtype.val := Measure.restrict_le_self
    _ ≤ _ := reflected_energy_free_density_le β hβ μ s h hs hh

theorem scalar_trial_density_away_terminal (β : ℝ) (hβ : 0 < β)
    (scalar : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 scalar)
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) (hsupp : parisiSupport scalar = Icc (0 : ℝ) q) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ lam : ℝ, lam ≤ β →
      (scalarTrialStieltjes β hβ.le lam scalar).measure.restrict ({q}ᶜ) ≤
        ENNReal.ofReal L • volume := by
  obtain ⟨L, hL, hDom⟩ := scalar_trial_density_domination β hβ scalar hmin q hq hsupp
  refine ⟨L, hL, ?_⟩
  intro lam hlam
  have hz := (scalar_trial_free_measure_above_terminal β hβ.le lam hlam scalar q hsupp).1
  have he : ({q}ᶜ : Set ℝ) = Iio q ∪ Ioi q := by
    ext x
    simp only [mem_compl_iff, mem_singleton_iff, mem_union, mem_Iio, mem_Ioi]
    exact ne_iff_lt_or_gt
  rw [he, Measure.restrict_union (by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact lt_asymm (show x < q from hx) (show q < x from hy)) measurableSet_Ioi,
    Measure.restrict_eq_zero.mpr hz, add_zero]
  exact (hDom lam).trans (by
    intro S
    change ENNReal.ofReal L * _ ≤ ENNReal.ofReal L * _
    gcongr
    exact Measure.restrict_le_self)

def regularizedSegmentStieltjes (β lam : ℝ) (hβ : 0 ≤ β)
    (scalar μ : Paper.ParisiMeasure) (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hh : 0 < h) (theta : ℝ) (_htheta : theta ∈ Icc (0 : ℝ) 1) : StieltjesFunction ℝ :=
  Real.toNNReal (1-theta) • scalarTrialStieltjes β hβ lam (reflectedParisiMeasure μ s h hs hh) +
    Real.toNNReal theta • scalarTrialStieltjes β hβ lam scalar

theorem regularizedSegmentStieltjes_apply_nonneg (β lam : ℝ) (hβ : 0 ≤ β)
    (scalar μ : Paper.ParisiMeasure) (s h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) (1 / 2)) (hroot : β*s=lam)
    (theta : ℝ) (htheta : theta ∈ Icc (0 : ℝ) 1) (x : ℝ) (hx : 0 ≤ x) :
    regularizedSegmentStieltjes β lam hβ scalar μ s h hs hh.1 theta htheta x =
      (1-theta)*β*parisiCDF (reflectedParisiMeasure μ s h hs hh.1) x +
        theta*scalarTrialProfile β lam scalar x := by
  have hr := (reflected_energy_root β μ s h hs hh).trans hroot
  have hc : lam ≤ β*parisiCDF (reflectedParisiMeasure μ s h hs hh.1) x := by
    rw [← hr]
    exact mul_le_mul_of_nonneg_left (parisiCDF_monotone _ hx) hβ
  change ((Real.toNNReal (1-theta) : ℝ))*max lam
    (β*parisiCDF (reflectedParisiMeasure μ s h hs hh.1) x) +
    ((Real.toNNReal theta : ℝ))*scalarTrialProfile β lam scalar x = _
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr htheta.2), Real.coe_toNNReal _ htheta.1,
    max_eq_right hc]
  ring

theorem regularizedSegmentStieltjes_density_away_terminal (β : ℝ) (hβ : 0 < β)
    (scalar : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 scalar)
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) (hsupp : parisiSupport scalar = Icc (0 : ℝ) q) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ μ : Paper.ParisiMeasure, ∀ s h : ℝ,
      ∀ hs : s ∈ Icc (0 : ℝ) 1, ∀ hh : h ∈ Ioc (0 : ℝ) (1 / 2),
      ∀ theta : ℝ, ∀ htheta : theta ∈ Icc (0 : ℝ) 1,
      h * L ≤ β →
      (regularizedSegmentStieltjes β (β*s) hβ.le scalar μ s h hs hh.1 theta htheta).measure.restrict
        ({q}ᶜ) ≤ ENNReal.ofReal (2*β/h) • volume := by
  obtain ⟨L, hL, hDom⟩ := scalar_trial_density_away_terminal β hβ scalar hmin q hq hsupp
  refine ⟨L, hL, ?_⟩
  intro μ s h hs hh theta htheta hscale
  have hfirst := Measure.restrict_mono_measure
    (reflected_trial_stieltjes_density_le β (β*s) hβ.le μ s h hs hh rfl) ({q}ᶜ)
  have hsecond := hDom (β*s) (by nlinarith [hs.2])
  have hLsmall : L ≤ β/h := (le_div_iff₀ hh.1).mpr (by nlinarith)
  unfold regularizedSegmentStieltjes
  rw [StieltjesFunction.measure_add, StieltjesFunction.measure_smul,
    StieltjesFunction.measure_smul, Measure.restrict_add,
    Measure.restrict_smul, Measure.restrict_smul]
  intro S
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have h1 := (hfirst.trans Measure.restrict_le_self) S
  have h2 := hsecond S
  have hc1 : ((Real.toNNReal (1-theta)) : ℝ≥0∞) ≤ 1 := by
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (sub_nonneg.mpr htheta.2)]
    exact ENNReal.ofReal_le_one.mpr (by linarith [htheta.1])
  have hc2 : ((Real.toNNReal theta) : ℝ≥0∞) ≤ 1 := by
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ htheta.1]
    exact ENNReal.ofReal_le_one.mpr htheta.2
  change ((Real.toNNReal (1-theta) : ℝ≥0∞))*
      ((scalarTrialStieltjes β hβ.le (β*s) (reflectedParisiMeasure μ s h hs hh.1)).measure.restrict ({q}ᶜ)) S +
    ((Real.toNNReal theta : ℝ≥0∞))*
      ((scalarTrialStieltjes β hβ.le (β*s) scalar).measure.restrict ({q}ᶜ)) S ≤ _
  calc
    _ ≤ ENNReal.ofReal (β/h)*volume S + ENNReal.ofReal L*volume S :=
      add_le_add (by simpa only [one_mul, Measure.smul_apply, smul_eq_mul] using mul_le_mul hc1 h1 (by positivity) (by positivity))
        (by simpa only [one_mul, Measure.smul_apply, smul_eq_mul] using mul_le_mul hc2 h2 (by positivity) (by positivity))
    _ ≤ ENNReal.ofReal (β/h)*volume S + ENNReal.ofReal (β/h)*volume S := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hLsmall) (by positivity))
    _ = _ := by
      rw [← add_mul, ← ENNReal.ofReal_add (div_nonneg hβ.le hh.1.le) (div_nonneg hβ.le hh.1.le)]
      congr 2
      ring

end QuantitativeFollowup
