module
public import FourPapersCommon.TimeFTCExpectation

@[expose] public section

/-! The finite time-partition telescope and its quantitative expectation
error. All fundamental-theorem and Fubini conditions are proved from the
regularity data and genuine endpoint increment bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped BigOperators NNReal Topology
namespace FourPapersCommon
set_option maxHeartbeats 1500000
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {T : ℝ≥0}

def timeFTCIntegral (d : TimeFTCData Ω E T) (X : ℝ≥0 → Ω → E)
    (Z : Ω → ℝ) (sample : Ω) : ℝ :=
  ∫ s in Ioc 0 T,Z sample*d.ft s sample (X s sample) ∂nonnegativeLebesgueMeasure

private theorem integrableOn_timeFTC_path (d : TimeFTCData Ω E T)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X)) (Z : Ω → ℝ)
    (sample : Ω) : IntegrableOn (fun s : ℝ≥0 => Z sample*d.ft s sample (X s sample))
      (Ioc 0 T) nonnegativeLebesgueMeasure := by
  have hm : Measurable (fun s : ℝ≥0 => Z sample*d.ft s sample (X s sample)) :=
    measurable_const.mul (d.ft_measurable.comp
      (NNReal.continuous_coe.measurable.prodMk
        (measurable_const.prodMk hX.of_uncurry_right)))
  apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T)
    (C := ‖Z sample‖*(d.bound : ℝ))).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (d.ft_bound s ⟨s.coe_nonneg,show (s : ℝ) ≤ T from hs.2⟩ sample _) (norm_nonneg _)

private theorem integral_Ioc_eq_sub_primitive {μ : Measure ℝ≥0} {g : ℝ≥0 → ℝ}
    (hg : IntegrableOn g (Ioc 0 T) μ) (a b : ℝ≥0) (hab : a ≤ b) (hb : b ≤ T) :
    (∫ s in Ioc a b,g s ∂μ) = (∫ s in Ioc 0 b,g s ∂μ)-(∫ s in Ioc 0 a,g s ∂μ) := by
  have hdiff : Ioc (0 : ℝ≥0) b \ Ioc 0 a = Ioc a b := by
    ext s
    simp only [Set.mem_sdiff,mem_Ioc]
    constructor
    · rintro ⟨⟨hs0,hsb⟩,hnot⟩
      exact ⟨lt_of_not_ge (fun hsa => hnot ⟨hs0,hsa⟩),hsb⟩
    · rintro ⟨has,hsb⟩
      exact ⟨⟨lt_of_le_of_lt bot_le has,hsb⟩,fun h=>not_le_of_gt has h.2⟩
  rw [← hdiff]
  exact setIntegral_sdiff measurableSet_Ioc
    (hg.mono_set (Ioc_subset_Ioc_right hb)) (Ioc_subset_Ioc_right hab)

theorem timeRightPartitionSum_sub_integral (d : TimeFTCData Ω E T)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X)) (Z : Ω → ℝ)
    {N : ℕ} (hN : 0 < N) (sample : Ω) :
    timeRightPartitionSum d X Z N sample-timeFTCIntegral d X Z sample =
      ∑ j∈Finset.range N,timeFTCCellError d X Z
        (uniformPartitionTime T N j) (uniformPartitionTime T N (j+1)) sample := by
  let a : ℕ → ℝ≥0 := uniformPartitionTime T N
  let g : ℝ≥0 → ℝ := fun s => Z sample*d.ft s sample (X s sample)
  have hg := integrableOn_timeFTC_path d X hX Z sample
  have hcell (j : ℕ) (hj : j < N) : timeFTCCellError d X Z (a j) (a (j+1)) sample =
      Z sample*(d.f (a (j+1)) sample (X (a (j+1)) sample)-d.f (a j) sample (X (a (j+1)) sample))-
        ((∫ s in Ioc 0 (a (j+1)),g s ∂nonnegativeLebesgueMeasure)-
          ∫ s in Ioc 0 (a j),g s ∂nonnegativeLebesgueMeasure) := by
    have hab : a j ≤ a (j+1) := monotone_uniformPartitionTime T N (Nat.le_add_right _ _)
    have hb : a (j+1) ≤ T :=
      (uniformPartitionTime_mem_Icc_of_le T hN (Nat.succ_le_iff.mpr hj)).2
    have hm : Measurable (fun s : ℝ≥0 => Z sample*d.ft s sample (X (a (j+1)) sample)) := by
      exact measurable_const.mul (d.ft_measurable.comp
        (NNReal.continuous_coe.measurable.prodMk (measurable_const.prodMk measurable_const)))
    have hi : IntegrableOn (fun s : ℝ≥0 => Z sample*d.ft s sample (X (a (j+1)) sample))
        (Ioc (a j) (a (j+1))) nonnegativeLebesgueMeasure := by
      apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top _ _)
        (C := ‖Z sample‖*(d.bound : ℝ))).mono' hm.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (d.ft_bound s ⟨s.coe_nonneg,(show (s : ℝ) ≤ a (j+1) from hs.2).trans
          (show (a (j+1) : ℝ≥0) ≤ T from hb)⟩ sample _) (norm_nonneg _)
    have hig : IntegrableOn g (Ioc (a j) (a (j+1))) nonnegativeLebesgueMeasure :=
      hg.mono_set (fun s hs=>⟨lt_of_le_of_lt bot_le hs.1,hs.2.trans hb⟩)
    unfold timeFTCCellError
    simp_rw [mul_sub]
    rw [integral_sub hi hig,integral_const_mul,
      ← d.increment_eq_integral (a j) (a (j+1)) hab hb,
      integral_Ioc_eq_sub_primitive hg (a j) (a (j+1)) hab hb]
    dsimp only [g]
    ring
  have htel := Finset.sum_range_sub (fun j => ∫ s in Ioc 0 (a j),g s ∂nonnegativeLebesgueMeasure) N
  have hzero : a 0 = 0 := by simp [a,uniformPartitionTime]
  have hlast : a N = T := by
    simp [a,uniformPartitionTime,ne_of_gt hN]
  rw [hlast,hzero] at htel
  simp only [Ioc_self,Measure.restrict_empty,integral_zero_measure,sub_zero] at htel
  rw [Finset.sum_congr rfl (fun j hj=>hcell j (Finset.mem_range.mp hj)),Finset.sum_sub_distrib,htel]
  rfl

end FourPapersCommon
