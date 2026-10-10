module
public import QuantitativePaper.VectorDirectionalDecayBounded
public import QuantitativePaper.VectorDirectionTruncation

@[expose] public section

/-! Directional covariance decay for every square-integrable random direction
measurable in the earlier whole past. Bounded truncation removes the uniform
bound without assuming any target covariance evolution. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal ENNReal Topology
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem vectorDirectionCovariance_decay (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β≠0) (ht : t<1)
    (r q : Paper.Overlap) (hrq : r≤q)
    (b : VectorDisorderBrownianSample n→Field n)
    (hb : Measurable[vectorBrownianFiltration n (r:ℝ).toNNReal] b)
    (hb2 : MemLp b 2 (vectorMeasureDisorderTilt μ β t a))
    (hden : 0<((1-t)*β^2)*∫u in (r:ℝ)..(q:ℝ),(Paper.parisiCDF μ u)^2) :
    vectorDirectionCovariance μ β t a ht.le b q≤
      (∫sample,‖b sample‖^2∂vectorMeasureDisorderTilt μ β t a)/
        (((1-t)*β^2)*∫u in (r:ℝ)..(q:ℝ),(Paper.parisiCDF μ u)^2) := by
  have hbm : Measurable b := hb.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hi : Integrable (fun sample=>‖b sample‖^2) (vectorMeasureDisorderTilt μ β t a) := by
    have hi := hb2.norm.integrable_mul hb2.norm
    change Integrable (fun sample=>‖b sample‖*‖b sample‖) _ at hi
    simpa only [pow_two] using hi
  have hlim := tendsto_integral_truncateVectorDirection_covariance μ β t a ht.le q b hbm hb2
  apply le_of_tendsto hlim
  exact .of_forall fun k=>by
    have hk := vectorDirectionCovariance_decay_bounded hn μ β t a hβ ht r q hrq
      (truncateVectorDirection b k) (measurable_truncateVectorDirection b hb k) (k:ℝ≥0)
      (fun sample=>by simpa only [NNReal.coe_natCast] using norm_truncateVectorDirection_le b k sample) hden
    have hbK := memLp_truncateVectorDirection μ β t a b hbm hb2 k
    have hiK : Integrable (fun sample=>‖truncateVectorDirection b k sample‖^2)
        (vectorMeasureDisorderTilt μ β t a) := by
      have hiK := hbK.norm.integrable_mul hbK.norm
      change Integrable (fun sample=>‖truncateVectorDirection b k sample‖*‖truncateVectorDirection b k sample‖) _ at hiK
      simpa only [pow_two] using hiK
    have hB := integral_mono hiK hi (fun sample=>pow_le_pow_left₀ (norm_nonneg _)
      (norm_truncateVectorDirection_le_original b k sample) 2)
    exact hk.trans (div_le_div_of_nonneg_right hB hden.le)

theorem vectorDirectionCovariance_decay_of_root_mass (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β t a s : ℝ) (hβ : β≠0) (ht : t<1)
    (hs : 0<s) (hμ : μ∈scalarFloor s)
    (r q : Paper.Overlap) (hrq : r<q)
    (b : VectorDisorderBrownianSample n→Field n)
    (hb : Measurable[vectorBrownianFiltration n (r:ℝ).toNNReal] b)
    (hb2 : MemLp b 2 (vectorMeasureDisorderTilt μ β t a)) :
    vectorDirectionCovariance μ β t a ht.le b q≤
      (∫sample,‖b sample‖^2∂vectorMeasureDisorderTilt μ β t a)/
        (((1-t)*β^2)*∫u in (r:ℝ)..(q:ℝ),(Paper.parisiCDF μ u)^2) :=
  vectorDirectionCovariance_decay hn μ β t a hβ ht r q hrq.le b hb hb2
    (vectorDirectionDenominator_pos μ β t s hβ ht hs hμ r q hrq)

end QuantitativePaper
