module
public import QuantitativeFollowup.RegularizedSegmentDensity
public import QuantitativeFollowup.ClippedTrialMeasureDensity
public import QuantitativeFollowup.ConcentratingMixedDensity

@[expose] public section

/-! Actual probability-measure density of the smoothed-to-trial segment.
Both the prescribed root atom and the terminal atom are retained; the
response tests vanish at precisely these excluded points. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FRSB
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000

theorem reflected_probability_density_off_root (beta : ℝ) (hb : 0≤beta)
    (μ : Paper.ParisiMeasure) (s h : ℝ) (hs : s∈Icc (0 : ℝ) 1)
    (hh : h∈Ioc (0 : ℝ) (1/2)) (q : ℝ) :
    (ENNReal.ofReal beta • (parisiCDFPrimitive (reflectedParisiMeasure μ s h hs hh.1)).measure).restrict
      ({(0 : ℝ),q}ᶜ) ≤ ENNReal.ofReal (beta/h) • volume := by
  let ν := reflectedParisiMeasure μ s h hs hh.1
  have hfloor := reflectedParisiMeasure_mem_floor μ s h hs hh
  have hmap : (ν:Measure Paper.Overlap).map Subtype.val =
      ENNReal.ofReal s • Measure.dirac (0 : ℝ)+(parisiFreeMeasure ν s).map Subtype.val := by
    rw [←root_add_parisiFreeMeasure ν s hs hfloor,
      Measure.map_add _ _ measurable_subtype_coe,Measure.map_smul _ measurable_subtype_coe.aemeasurable,
      Measure.map_dirac zeroOverlap]
    rfl
  rw [parisiCDFPrimitive_measure,hmap,smul_add,Measure.restrict_add]
  simp only [Measure.restrict_smul]
  rw [restrict_dirac' ((measurableSet_singleton q).insert 0).compl]
  simp only [mem_compl_iff, mem_insert_iff, true_or, not_true, ite_false,
    smul_zero, zero_add]
  rw [←Measure.restrict_smul]
  exact Measure.restrict_le_self.trans (reflected_energy_free_density_le beta hb μ s h hs hh)

theorem clipped_probability_density_off_root_terminal (beta lam : ℝ) (hb : 0<beta)
    (hlam : lam∈Icc (0 : ℝ) beta) (scalar : Paper.ParisiMeasure) (q L : ℝ)
    (hDom : (scalarTrialStieltjes beta hb.le lam scalar).measure.restrict ({q}ᶜ) ≤
      ENNReal.ofReal L • volume) :
    (ENNReal.ofReal beta • (parisiCDFPrimitive
      (scalarClippedTrialMeasure (lam/beta)
        ⟨div_nonneg hlam.1 hb.le,(div_le_one hb).mpr hlam.2⟩ scalar)).measure).restrict
      ({(0 : ℝ),q}ᶜ) ≤ ENNReal.ofReal L • volume := by
  let E : Set ℝ := {(0 : ℝ),q}ᶜ
  have hE : MeasurableSet E := ((measurableSet_singleton q).insert 0).compl
  rw [parisiCDFPrimitive_measure]
  change (ENNReal.ofReal beta •
    ((scalarClippedRealMeasure (lam/beta) scalar).comap (Subtype.val:Paper.Overlap→ℝ)).map Subtype.val).restrict E≤_
  rw [map_comap_subtype_coe measurableSet_Icc]
  have hfirst : (ENNReal.ofReal beta • (scalarClippedRealMeasure (lam/beta) scalar).restrict
      (Icc (0 : ℝ) 1)).restrict E ≤
      (ENNReal.ofReal beta • scalarClippedRealMeasure (lam/beta) scalar).restrict E := by
    apply Measure.restrict_mono_measure
    intro S
    simp only [Measure.smul_apply,smul_eq_mul]
    gcongr
    exact Measure.restrict_le_self
  apply hfirst.trans
  rw [scalarClippedRealMeasure,smul_add,Measure.restrict_add]
  simp only [Measure.restrict_smul]
  rw [restrict_dirac' hE]
  have hz : (0 : ℝ)∉E := by simp [E]
  simp only [hz, ite_false, smul_zero, add_zero]
  have hMeasure : ENNReal.ofReal beta •
      (scalarTrialStieltjes 1 (by norm_num) (lam/beta) scalar).measure=
      (scalarTrialStieltjes beta hb.le lam scalar).measure := by
    rw [←scalarTrialStieltjes_scale beta lam hb scalar,StieltjesFunction.measure_smul]
    congr 1
  rw [←Measure.restrict_smul,hMeasure]
  exact (Measure.restrict_mono (by intro x hx; exact fun h =>hx (Or.inr (by simpa using h)))
    le_rfl).trans hDom

theorem regularized_probability_segment_density (beta : ℝ) (hb : 0<beta)
    (scalar : Paper.ParisiMeasure) (hmin : IsParisiMinimizer beta 0 scalar)
    (q : ℝ) (hq : q∈Ioo (0 : ℝ) 1) (hsupp : parisiSupport scalar=Icc (0 : ℝ) q) :
    ∃L : ℝ,1≤L ∧ ∀μ : Paper.ParisiMeasure,∀lam h theta : ℝ,
      ∀hlam : lam∈Icc (0 : ℝ) beta,∀hh : h∈Ioc (0 : ℝ) (1/2),
      theta∈Icc (0 : ℝ) 1→h*L≤beta→
      (ENNReal.ofReal beta • (parisiCDFPrimitive (parisiMix
        (reflectedParisiMeasure μ (lam/beta) h
          ⟨div_nonneg hlam.1 hb.le,(div_le_one hb).mpr hlam.2⟩ hh.1)
        (scalarClippedTrialMeasure (lam/beta)
          ⟨div_nonneg hlam.1 hb.le,(div_le_one hb).mpr hlam.2⟩ scalar) theta)).measure).restrict
        ({(0 : ℝ),q}ᶜ)≤ENNReal.ofReal (2*beta/h) • volume := by
  obtain ⟨L,hL,hDom⟩ := scalar_trial_density_away_terminal beta hb scalar hmin q hq hsupp
  refine ⟨L,hL,?_⟩
  intro μ lam h theta hlam hh htheta hscale
  have hfirst := reflected_probability_density_off_root beta hb.le μ (lam/beta) h
    ⟨div_nonneg hlam.1 hb.le,(div_le_one hb).mpr hlam.2⟩ hh q
  have hsecond := clipped_probability_density_off_root_terminal beta lam hb hlam scalar q L
    (hDom lam hlam.2)
  have hsmall : L≤beta/h := (le_div_iff₀ hh.1).mpr (by nlinarith)
  rw [parisiCDFPrimitive_measure,parisiMix_measure _ _ theta htheta,
    Measure.map_add _ _ measurable_subtype_coe,
    Measure.map_smul _ measurable_subtype_coe.aemeasurable,
    Measure.map_smul _ measurable_subtype_coe.aemeasurable,
    smul_add,Measure.restrict_add,smul_comm (ENNReal.ofReal beta),
    Measure.restrict_smul,smul_comm (ENNReal.ofReal beta),Measure.restrict_smul]
  rw [parisiCDFPrimitive_measure] at hfirst hsecond
  intro S
  simp only [Measure.add_apply,Measure.restrict_smul,Measure.smul_apply,smul_eq_mul]
  have hc1 : ENNReal.ofReal (1-theta)≤1 := ENNReal.ofReal_le_one.mpr (by linarith [htheta.1])
  have hc2 : ENNReal.ofReal theta≤1 := ENNReal.ofReal_le_one.mpr htheta.2
  have hh1 := mul_le_mul hc1 (hfirst S) (by positivity) (by positivity)
  have hh2 := mul_le_mul hc2 (hsecond S) (by positivity) (by positivity)
  have hlo := ENNReal.ofReal_le_ofReal hsmall
  calc
    _≤ENNReal.ofReal (beta/h)*volume S+ENNReal.ofReal L*volume S := by
      simpa only [one_mul,Measure.restrict_smul,Measure.smul_apply,smul_eq_mul] using add_le_add hh1 hh2
    _≤ENNReal.ofReal (beta/h)*volume S+ENNReal.ofReal (beta/h)*volume S :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hlo (by positivity))
    _=ENNReal.ofReal (2*beta/h)*volume S := by
      rw [←add_mul,←ENNReal.ofReal_add (div_nonneg hb.le hh.1.le) (div_nonneg hb.le hh.1.le)]
      congr 2
      ring

end QuantitativeFollowup
