module
public import QuantitativePaper.VectorDirectionalIsometry
public import QuantitativePaper.VectorMeasureDirectionCovariance
public import FourPapersCommon.IntegralDecayRiccati

@[expose] public section

/-! Exact covariance evolution in a bounded direction known in the earlier
whole past. The stochastic isometry and conditional covariance identity have
both been proved for the actual physical process. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal ENNReal Topology
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def vectorDirectionCovariance (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (b : VectorDisorderBrownianSample n→Field n) (q : Paper.Overlap) : ℝ :=
  ∫sample,vectorMeasureCovarianceQuadratic μ β t a ht q sample (b sample)
    ∂vectorMeasureDisorderTilt μ β t a

theorem vectorDirectionCovariance_nonneg (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (b : VectorDisorderBrownianSample n→Field n)
    (q : Paper.Overlap) : 0≤vectorDirectionCovariance μ β t a ht.le b q := by
  apply integral_nonneg_of_ae
  filter_upwards [vectorMeasureCovarianceQuadratic_nonneg μ β t a hβ ht q] with sample hs
  exact hs (b sample)

theorem vectorDirectionEnergy_nonneg (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (b : VectorDisorderBrownianSample n→Field n) (q : Paper.Overlap) :
    0≤vectorDirectionEnergy μ β t a ht b q :=
  integral_nonneg fun _=>sq_nonneg _

theorem vectorDirectionCovariance_interval_evolution (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β≠0) (ht : t<1)
    (r q : Paper.Overlap) (hrq : r≤q) (b : VectorDisorderBrownianSample n→Field n)
    (hb : Measurable[vectorBrownianFiltration n (r:ℝ).toNNReal] b)
    (K : ℝ≥0) (hK : ∀sample,‖b sample‖≤K) :
    vectorDirectionCovariance μ β t a ht.le b q=
      vectorDirectionCovariance μ β t a ht.le b r-
        ∫s in (r:ℝ)..(q:ℝ),((1-t)*β^2)*vectorDirectionEnergy μ β t a ht.le b
          (projIcc 0 1 zero_le_one s) := by
  have he := vectorMeasure_random_covariance_decay μ β t a hβ ht r q hrq b hb K hK
  rw [vectorMean_direction_increment_isometry hn μ β t a hβ ht r q hrq b hb K hK] at he
  simpa only [vectorDirectionCovariance,intervalIntegral.integral_const_mul] using he

theorem vectorDirectionCovariance_curve_regular (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β≠0) (ht : t<1)
    (r q : Paper.Overlap) (hrq : r≤q) (b : VectorDisorderBrownianSample n→Field n)
    (hb : Measurable[vectorBrownianFiltration n (r:ℝ).toNNReal] b)
    (K : ℝ≥0) (hK : ∀sample,‖b sample‖≤K) :
    AbsolutelyContinuousOnInterval
      (fun s=>vectorDirectionCovariance μ β t a ht.le b (projIcc 0 1 zero_le_one s)) r q ∧
    AntitoneOn (fun s=>vectorDirectionCovariance μ β t a ht.le b (projIcc 0 1 zero_le_one s)) (Icc (r:ℝ) q) ∧
    (∀ᵐ s : ℝ,s∈Icc (r:ℝ) q→HasDerivAt
      (fun u=>vectorDirectionCovariance μ β t a ht.le b (projIcc 0 1 zero_le_one u))
      (-(((1-t)*β^2)*vectorDirectionEnergy μ β t a ht.le b (projIcc 0 1 zero_le_one s))) s) := by
  have hbm : Measurable b := hb.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hf : Continuous (fun s : ℝ=>((1-t)*β^2)*vectorDirectionEnergy μ β t a ht.le b
      (projIcc 0 1 zero_le_one s)) :=
    ((continuous_vectorDirectionEnergy μ β t a ht.le b hbm K hK).comp continuous_projIcc).const_mul ((1-t)*β^2)
  apply integral_decay_curve_regular hrq (hf.intervalIntegrable _ _)
  · intro s _
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr ht.le) (sq_nonneg β))
      (vectorDirectionEnergy_nonneg μ β t a ht.le b _)
  · intro s hs
    let u : Paper.Overlap := ⟨s,⟨r.property.1.trans hs.1,hs.2.trans q.property.2⟩⟩
    have hu : r≤u := hs.1
    simpa only [u,projIcc_of_mem zero_le_one r.property,projIcc_of_mem zero_le_one u.property]
      using vectorDirectionCovariance_interval_evolution hn μ β t a hβ ht r u hu b hb K hK

end QuantitativePaper
