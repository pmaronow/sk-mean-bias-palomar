module
public import QuantitativeFollowup.FollowupCavityResidualPenalty

@[expose] public section

/-! The literal strict-future covariance formula for the actual nonnegative
penalty. Endpoint atoms are retained by the strict restrictions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper Paper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128

def cavityScalarConditionalCovariance (β : ℝ) (μ : Paper.ParisiMeasure)
    (r p l : Paper.Overlap) : ℝ :=
  covariance (cavityScalarFutureSquare β μ r p) (cavityScalarFutureSquare β μ r l)
    canonicalBrownianMeasure

def cavityRestConditionalCovariance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p l : Paper.Overlap) : ℝ :=
  ∫ω,(cavityRestSelfOverlap D μ p ω-cavityRestFutureSquare D μ r p ω)*
    (cavityRestSelfOverlap D μ l ω-cavityRestFutureSquare D μ r l ω)
    ∂anisotropicMeasureSampleLaw D μ a

theorem cavityScalarFutureCovariance_eq_mask (β : ℝ) (μ : Paper.ParisiMeasure)
    (r p l : Paper.Overlap) :
    cavityScalarFutureCovariance β μ r p l=
      if r<p then if r<l then cavityScalarConditionalCovariance β μ r p l else 0 else 0 := by
  by_cases hp : r<p
  · by_cases hl : r<l
    · simpa only [hp,hl,ite_eq_left,cavityScalarConditionalCovariance] using
        cavityScalarFutureCovariance_eq_covariance β μ r p l hp hl
    · simp [cavityScalarFutureCovariance,cavityScalarFutureCenteredTail,hl]
  · simp [cavityScalarFutureCovariance,cavityScalarFutureCenteredTail,hp]

theorem cavityRestResidualCovariance_eq_mask (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p l : Paper.Overlap) :
    cavityRestResidualCovariance D μ a r p l=
      if r<p then if r<l then cavityRestConditionalCovariance D μ a r p l else 0 else 0 := by
  by_cases hp : r<p
  · by_cases hl : r<l
    · simp only [cavityRestResidualCovariance,cavityRestFutureResidualTail,hp,hl,
        ite_eq_left,cavityRestConditionalCovariance]
    · simp [cavityRestResidualCovariance,cavityRestFutureResidualTail,hl]
  · simp [cavityRestResidualCovariance,cavityRestFutureResidualTail,hp]

theorem cavityResidualPenaltyAt_eq_strict_future (β : ℝ) (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) :
    cavityResidualPenaltyAt β D μ a r=
      ∫p in Ioi r,∫l in Ioi r,cavityScalarConditionalCovariance β μ r p l*
        cavityRestConditionalCovariance D μ a r p l
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a := by
  let W : Paper.Overlap×Paper.Overlap→ℝ:=fun pq=>
    cavityScalarFutureCovariance β μ r pq.1 pq.2*cavityRestResidualCovariance D μ a r pq.1 pq.2
  have hm : Measurable W := by
    exact ((measurable_cavityScalarFutureCovariance β μ).comp
      (measurable_const.prodMk measurable_id)).mul
      ((measurable_cavityRestResidualCovariance D μ a).comp
        (measurable_const.prodMk measurable_id))
  have hb (pq : Paper.Overlap×Paper.Overlap) : ‖W pq‖≤(1:ℝ) := by
    dsimp only [W]
    rw [norm_mul]
    exact (mul_le_mul (cavityScalarFutureCovariance_norm_le β μ r _ _)
      (cavityRestResidualCovariance_norm_le D μ a r _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hi : Integrable W ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) :=
    (integrable_const 1).mono' hm.aestronglyMeasurable (.of_forall hb)
  change (∫pq,W pq ∂(parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a))=_
  rw [integral_prod W hi,←integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact .of_forall fun p=>by
    by_cases hp : r<p
    · rw [Set.indicator_of_mem (show p∈Ioi r from hp)]
      rw [←integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      exact .of_forall fun l=>by
        dsimp only [W]
        rw [cavityScalarFutureCovariance_eq_mask,cavityRestResidualCovariance_eq_mask]
        by_cases hl : r<l <;> simp [Set.indicator,mem_Ioi,hp,hl]
    · rw [Set.indicator_of_notMem (show p∉Ioi r from hp)]
      simp [W,cavityScalarFutureCovariance_eq_mask,hp]

theorem cavityRestConditionalCovariance_eq_fullPast (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p l : Paper.Overlap) (hrp : r≤p) (hrl : r≤l) :
    cavityRestConditionalCovariance D μ a r p l=
      ∫ω,(cavityRestSelfOverlap D μ p ω-(anisotropicMeasureSampleLaw D μ a)[cavityRestSelfOverlap D μ p|
        anisotropicBrownianFiltration n (r:ℝ).toNNReal] ω)*
        (cavityRestSelfOverlap D μ l ω-(anisotropicMeasureSampleLaw D μ a)[cavityRestSelfOverlap D μ l|
        anisotropicBrownianFiltration n (r:ℝ).toNNReal] ω) ∂anisotropicMeasureSampleLaw D μ a := by
  apply integral_congr_ae
  filter_upwards [cavityRestFutureSquare_condExp D μ a r p hrp,
    cavityRestFutureSquare_condExp D μ a r l hrl] with ω hp hl
  rw [hp,hl]

theorem cavityResidualPenalty_eq_printed (β : ℝ) (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    cavityResidualPenalty β D μ a=
      ∫r,∫p in Ioi r,∫l in Ioi r,
        covariance (cavityScalarFutureSquare β μ r p) (cavityScalarFutureSquare β μ r l)
          canonicalBrownianMeasure*
        (∫ω,(cavityRestSelfOverlap D μ p ω-(anisotropicMeasureSampleLaw D μ a)[cavityRestSelfOverlap D μ p|
            anisotropicBrownianFiltration n (r:ℝ).toNNReal] ω)*
          (cavityRestSelfOverlap D μ l ω-(anisotropicMeasureSampleLaw D μ a)[cavityRestSelfOverlap D μ l|
            anisotropicBrownianFiltration n (r:ℝ).toNNReal] ω) ∂anisotropicMeasureSampleLaw D μ a)
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a := by
  unfold cavityResidualPenalty
  apply integral_congr_ae
  exact .of_forall fun r=>by
    rw [cavityResidualPenaltyAt_eq_strict_future]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
    rw [cavityRestConditionalCovariance_eq_fullPast D μ a r p l hp.le hl.le]
    rfl

end QuantitativeFollowup
