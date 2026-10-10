module
public import QuantitativeFollowup.ScalarTrialMeasure

@[expose] public section

/-! Actual continuity of the constrained scalar minimum. The exact clipped-CDF
trial supplies a comparison measure; no continuity of a minimizer is assumed. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace QuantitativePaper

theorem zeroMass_eq_parisiCDF_zero (μ : ParisiMeasure) : zeroMass μ = parisiCDF μ 0 := by
  unfold zeroMass parisiCDF
  congr 2
  ext r
  constructor
  · intro hr
    have heq : r = zeroOverlap := hr
    rw [heq]
    change (0 : ℝ) ≤ 0
    exact le_rfl
  · intro hr
    apply Subtype.ext
    exact le_antisymm hr r.property.1

theorem scalarFloor_cdf_lower {s : ℝ} {μ : ParisiMeasure} (hμ : μ ∈ scalarFloor s)
    {q : ℝ} (hq : 0 ≤ q) : s ≤ parisiCDF μ q := by
  rw [mem_scalarFloor_iff,zeroMass_eq_parisiCDF_zero] at hμ
  exact hμ.trans (parisiCDF_monotone μ hq)

theorem clippedTrial_cdf_sub_le {s t : ℝ} (hst : s ≤ t) (ht : t ∈ Icc (0 : ℝ) 1)
    (μ : ParisiMeasure) (hμ : μ ∈ scalarFloor s) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    |parisiCDF (QuantitativeFollowup.scalarClippedTrialMeasure t ht μ) q-parisiCDF μ q| ≤ t-s := by
  rw [QuantitativeFollowup.scalarClippedTrialMeasure_cdf t ht μ q hq]
  rw [abs_of_nonneg (sub_nonneg.mpr (le_max_right _ _))]
  apply sub_le_iff_le_add.mpr
  apply max_le
  · linarith [scalarFloor_cdf_lower hμ hq.1]
  · linarith

theorem clippedTrial_cdfDistance_le {s t : ℝ} (hst : s ≤ t) (ht : t ∈ Icc (0 : ℝ) 1)
    (μ : ParisiMeasure) (hμ : μ ∈ scalarFloor s) :
    parisiCDFDistance (QuantitativeFollowup.scalarClippedTrialMeasure t ht μ) μ ≤ t-s := by
  unfold parisiCDFDistance
  calc
    _ ≤ ∫ q in (0 : ℝ)..1,t-s := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (parisiCDF_abs_diff_intervalIntegrable _ _ 0 1) intervalIntegrable_const
      intro q hq
      exact clippedTrial_cdf_sub_le hst ht μ hμ q hq
    _ = _ := by simp

theorem constrainedParisiValue_sub_le (β : ℝ) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    constrainedParisiValue β t-constrainedParisiValue β s ≤ 2*β^2*(t-s) := by
  let μ := constrainedParisiMinimizer β s hs.2
  let ν := QuantitativeFollowup.scalarClippedTrialMeasure t ht μ
  have hμ := constrainedParisiMinimizer_mem β s hs.2
  have hν := QuantitativeFollowup.scalarClippedTrialMeasure_mem_floor t ht μ
  have hp := constrainedParisiValue_le β t ht.2 ν hν
  have hb := FRSB.parisiPDEFunctional_measure_sub_le β 0 ν μ
  have hd := clippedTrial_cdfDistance_le hst ht μ hμ
  rw [constrainedParisiValue_eq_minimum β s hs.2]
  have hprod := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2*β^2)
  have hnorm := le_abs_self (scalarParisiFunctional β ν-scalarParisiFunctional β μ)
  rw [←Real.norm_eq_abs] at hnorm
  change ‖scalarParisiFunctional β ν-scalarParisiFunctional β μ‖ ≤ _ at hb
  linarith

theorem constrainedParisiValue_lipschitzOn (β : ℝ) :
    LipschitzOnWith (2*β^2).toNNReal (constrainedParisiValue β) (Icc (0 : ℝ) 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro s hs t ht
  rw [Real.dist_eq,Real.dist_eq,Real.coe_toNNReal _ (by positivity)]
  by_cases hst : s ≤ t
  · rw [abs_of_nonpos (sub_nonpos.mpr (constrainedParisiValue_mono β hst ht.2)),
      abs_of_nonpos (sub_nonpos.mpr hst)]
    have hh := constrainedParisiValue_sub_le β hs ht hst
    linarith
  · have hts := le_of_not_ge hst
    rw [abs_of_nonneg (sub_nonneg.mpr (constrainedParisiValue_mono β hts hs.2)),
      abs_of_nonneg (sub_nonneg.mpr hts)]
    exact constrainedParisiValue_sub_le β ht hs hts

theorem continuousOn_constrainedParisiValue (β : ℝ) :
    ContinuousOn (constrainedParisiValue β) (Icc (0 : ℝ) 1) :=
  (constrainedParisiValue_lipschitzOn β).continuousOn

end QuantitativePaper
