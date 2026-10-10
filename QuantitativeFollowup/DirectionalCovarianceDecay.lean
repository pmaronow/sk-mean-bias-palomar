module
public import QuantitativePaper.VectorDirectionalDecay

@[expose] public section

/-! Follow-up Lemma 4.1, with the actual profile, physical fractional tilt,
whole-past random direction, and literal squared-CDF denominator. No minimizing
hypothesis is needed. The root mass may be any positive feasible mass. -/
noncomputable section
open MeasureTheory Set QuantitativePaper
open scoped NNReal ENNReal
namespace QuantitativeFollowup
variable {n : ℕ}

theorem directional_covariance_decay (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β t s : ℝ) (hβ : β≠0) (ht : t<1)
    (hs : 0<s) (hμ : μ∈scalarFloor s)
    (r q : Paper.Overlap) (hrq : r<q)
    (b : VectorDisorderBrownianSample n→Field n)
    (hb : Measurable[vectorBrownianFiltration n (r:ℝ).toNNReal] b)
    (hb2 : MemLp b 2 (vectorMeasureDisorderTilt μ β t s)) :
    let I := ((1-t)*β^2)*∫u in (r:ℝ)..(q:ℝ),(Paper.parisiCDF μ u)^2
    ((1-t)*β^2)*s^2*((q:ℝ)-r)≤I ∧ 0<I ∧
      (∫sample,vectorMeasureCovarianceQuadratic μ β t s ht.le q sample (b sample)
        ∂vectorMeasureDisorderTilt μ β t s)≤
        (∫sample,‖b sample‖^2∂vectorMeasureDisorderTilt μ β t s)/I := by
  dsimp only
  exact ⟨vectorDirectionDenominator_lower μ β t s ht.le hs.le hμ r q hrq.le,
    vectorDirectionDenominator_pos μ β t s hβ ht hs hμ r q hrq,
    vectorDirectionCovariance_decay_of_root_mass hn μ β t s s hβ ht hs hμ r q hrq b hb hb2⟩

end QuantitativeFollowup
