module
public import FourPapersCommon.TimeFTCPartitionExpectation

@[expose] public section

/-! Actual integrability of bounded measurable time integrals and their
interval subtraction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal Topology
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω]

theorem integrableOn_bounded_time_function (F : ℝ≥0 → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (K : ℝ≥0) (b : ℝ≥0)
    (hK : ∀ s∈Icc 0 b,∀ ω,‖F s ω‖ ≤ K) (ω : Ω) :
    IntegrableOn (fun s=>F s ω) (Ioc 0 b) nonnegativeLebesgueMeasure := by
  apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 b)
    (C := (K : ℝ))).mono' (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact hK s ⟨bot_le,hs.2⟩ ω

theorem integrable_bounded_time_integral (P : Measure Ω) [IsFiniteMeasure P]
    (F : ℝ≥0 → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (K : ℝ≥0) (b : ℝ≥0) (hK : ∀ s∈Icc 0 b,∀ ω,‖F s ω‖ ≤ K) :
    Integrable (fun ω=>∫ s in Ioc 0 b,F s ω ∂nonnegativeLebesgueMeasure) P := by
  haveI : IsFiniteMeasure (nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) b)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 b)⟩
  have hm := hF.stronglyMeasurable.integral_prod_left'
    (μ := nonnegativeLebesgueMeasure.restrict (Ioc 0 b))
  apply Integrable.of_bound hm.aestronglyMeasurable ((K : ℝ)*b)
  apply Eventually.of_forall
  intro ω
  have hb := norm_integral_le_of_norm_le_const (μ := nonnegativeLebesgueMeasure.restrict (Ioc 0 b))
    (f := fun s=>F s ω) (C := (K : ℝ))
    ((ae_restrict_mem measurableSet_Ioc).mono (fun s hs=>hK s ⟨bot_le,hs.2⟩ ω))
  simpa only [Measure.real,Measure.restrict_apply_univ,nonnegativeLebesgueMeasure_Ioc,
    NNReal.coe_zero,sub_zero,ENNReal.toReal_ofReal b.coe_nonneg,Function.uncurry_apply_pair] using hb

theorem bounded_time_integral_sub (F : ℝ≥0 → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (K : ℝ≥0) (a b : ℝ≥0) (hab : a ≤ b)
    (hK : ∀ s∈Icc 0 b,∀ ω,‖F s ω‖ ≤ K) (ω : Ω) :
    (∫ s in Ioc 0 b,F s ω ∂nonnegativeLebesgueMeasure)-
      (∫ s in Ioc 0 a,F s ω ∂nonnegativeLebesgueMeasure)=
      ∫ s in Ioc a b,F s ω ∂nonnegativeLebesgueMeasure := by
  have he : Ioc (0 : ℝ≥0) b \ Ioc 0 a=Ioc a b := by
    ext s
    simp only [Set.mem_sdiff,mem_Ioc]
    constructor
    · rintro ⟨⟨hs0,hsb⟩,hna⟩
      exact ⟨lt_of_not_ge (fun hsa=>hna ⟨hs0,hsa⟩),hsb⟩
    · rintro ⟨has,hsb⟩
      exact ⟨⟨lt_of_le_of_lt bot_le has,hsb⟩,fun hs=>not_le_of_gt has hs.2⟩
  rw [←he]
  exact (setIntegral_sdiff measurableSet_Ioc
    (integrableOn_bounded_time_function F hF K b hK ω) (Ioc_subset_Ioc_right hab)).symm

def TimeFTCData.restrictHorizon {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {b : ℝ≥0} (d : TimeFTCData Ω E b) (a : ℝ≥0) (hab : a ≤ b) : TimeFTCData Ω E a where
  f := d.f
  ft := d.ft
  f_measurable := d.f_measurable
  ft_measurable := d.ft_measurable
  f_continuous := fun ω x=>(d.f_continuous ω x).mono (Icc_subset_Icc_right (show (a : ℝ)≤b from hab))
  derivative := fun ω x r hr=>d.derivative ω x r ⟨hr.1,hr.2.trans_le (show (a : ℝ)≤b from hab)⟩
  ft_continuous := d.ft_continuous
  bound := d.bound
  spatialLip := d.spatialLip
  ft_bound := fun r hr=>d.ft_bound r ⟨hr.1,hr.2.trans (show (a : ℝ)≤b from hab)⟩
  ft_lipschitz := fun r hr=>d.ft_lipschitz r ⟨hr.1,hr.2.trans (show (a : ℝ)≤b from hab)⟩

end FourPapersCommon
