module
public import QuantitativeFollowup.FollowupCavityGeneratedMarkCounts
public import QuantitativeFollowup.FollowupCavityThirdMoment

@[expose] public section

/-! Actual native cubic moments integrated against explicit generated
mark measures. The measure bound is derived from the program itself. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open QuantitativePaper
variable {n m : ℕ}
set_option maxHeartbeats 900000

theorem cavityGenerated_free_mass_le_one (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a) :
    parisiFreeMeasure μ a univ ≤ 1 := by
  rw [parisiFreeMeasure_univ]
  simpa only [ENNReal.ofReal_one] using
    ENNReal.ofReal_le_ofReal (sub_le_self (1 : ℝ) ha)

theorem cavityGenerated_coordinate_cubic_le (D : AnisotropicSpinModel (n + 1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (i : Fin m) :
    (∫ h, cavityCubicPairMoment D μ a (h i) ∂P.measure (parisiFreeMeasure μ a)) ≤
      (P.budget : ℝ) * cavityThirdMoment D μ a := by
  have hν := cavityGenerated_free_mass_le_one μ a ha
  have hχ := (continuous_cavityCubicPairMoment D μ a).measurable
  have hi := (integrable_cavityCubicPairMoment D μ a).smul_measure
    (ENNReal.natCast_ne_top P.budget)
  have hh := integral_mono_measure (P.coordinate_marginal_le_budget _ hν i)
    (Filter.Eventually.of_forall fun q => (cavityCubicPairMoment_bounds D μ a q).1) hi
  rw [integral_smul_measure] at hh
  rw [integral_map (measurable_pi_apply i).aemeasurable
    hχ.aestronglyMeasurable] at hh
  simpa only [cavityGeneratedHistoryMarks, ENNReal.toReal_natCast, smul_eq_mul,
    cavityThirdMoment] using hh

theorem cavityGenerated_sum_marks_cubic_le (D : AnisotropicSpinModel (n + 1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (P : CavityGeneratedMarkProgram Paper.Overlap m) :
    (∫ h, ∑ i : Fin m, cavityCubicPairMoment D μ a (h i)
        ∂P.measure (parisiFreeMeasure μ a)) ≤
      (m : ℝ) * P.budget * cavityThirdMoment D μ a := by
  haveI := P.isFiniteMeasure_measure _ (cavityGenerated_free_mass_le_one μ a ha)
  have hi (i : Fin m) : Integrable (fun h => cavityCubicPairMoment D μ a (h i))
      (P.measure (parisiFreeMeasure μ a)) := by
    apply (integrable_const (8 : ℝ)).mono'
      ((continuous_cavityCubicPairMoment D μ a).measurable.comp
        (cavityGeneratedHistoryMarks_measurable (Q := Paper.Overlap) i)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun h => by
      change ‖cavityCubicPairMoment D μ a (h i)‖ ≤ 8
      rw [Real.norm_of_nonneg (cavityCubicPairMoment_bounds D μ a (h i)).1]
      exact (cavityCubicPairMoment_bounds D μ a (h i)).2
  rw [integral_finset_sum _ (fun i _ => hi i)]
  apply (Finset.sum_le_sum (fun i _ => cavityGenerated_coordinate_cubic_le D μ a ha P i)).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end QuantitativeFollowup
