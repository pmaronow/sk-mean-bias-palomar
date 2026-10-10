module
public import QuantitativeFollowup.ScalarSquareIto
public import QuantitativeFollowup.ScalarPotentialIto
public import QuantitativeFollowup.ScalarTailEquality

@[expose] public section

/-! The literal clipping evolution and localization identities. All time
regularity, source integrability, endpoint limits and terminal equality
are discharged for the actual minimizing measure and its clipped trial. -/
noncomputable section
open Set MeasureTheory Filter Paper FRSB FourPapersCommon
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 500000

theorem continuous_scalarSquareDifferenceMoment (β : ℝ) (hβ : β≠0)
    (μ ν : Paper.ParisiMeasure) : Continuous (scalarSquareDifferenceMoment β hβ μ ν) := by
  apply continuous_ito_bounded_observable_expectation
    (boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).continuous_state
    (boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).adapted_state
    (fun t x=>scalarGradientDifference β μ ν (t,x)^2)
    ((continuous_scalarGradientDifference β μ ν).pow 2) 4
  intro t x
  rw [norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_scalarGradientDifference_le β μ ν (t,x)) 2).trans_eq (by norm_num)

theorem scalarSquareDifferenceMoment_nonneg (β : ℝ) (hβ : β≠0)
    (μ ν : Paper.ParisiMeasure) (t : ℝ≥0) : 0 ≤ scalarSquareDifferenceMoment β hβ μ ν t :=
  integral_nonneg (fun _=>sq_nonneg _)

theorem scalarClipped_square_interval (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (l r : ℝ≥0) (hlr : l≤r) (hrq : (r:ℝ)<q) :
    scalarSquareDifferenceMoment β hβ μ (scalarClippedTrialMeasure s hs μ) r-
      scalarSquareDifferenceMoment β hβ μ (scalarClippedTrialMeasure s hs μ) l=
      ∫t in (l:ℝ)..(r:ℝ),∫ω,
        scalarClippingSquareSource β μ (scalarClippedTrialMeasure s hs μ)
          (t,selectedParisiItoState β 0 hβ μ t.toNNReal ω)∂canonicalBrownianMeasure := by
  apply scalarSquareDifferenceMoment_interval_integral β hβ μ _
    (scalarSupportCDF β μ q hq.1.le) (fun t=>max s (scalarSupportCDF β μ q hq.1.le t))
    (continuous_scalarSupportCDF β hβ μ hmin q hq hsupp)
    (continuous_const.max (continuous_scalarSupportCDF β hβ μ hmin q hq hsupp)) q hq.2.le _ _ l r hlr hrq
  · intro t ht
    exact (scalarSupportCDF_eq_cdf β hβ μ hmin q hq hsupp t ⟨ht.1.le,ht.2⟩).symm
  · intro t ht
    change parisiCDF (scalarClippedTrialMeasure s hs μ) t=max s (scalarSupportCDF β μ q hq.1.le t)
    rw [scalarClippedTrialMeasure_cdf s hs μ t ⟨ht.1.le,ht.2.le.trans hq.2.le⟩,
      scalarSupportCDF_eq_cdf β hβ μ hmin q hq hsupp t ⟨ht.1.le,ht.2⟩]

theorem scalarClipped_potential_interval (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (l r : ℝ≥0) (hlr : l≤r) (hrq : (r:ℝ)<q) :
    (∫ω,parisiPotential β (scalarClippedTrialMeasure s hs μ) (r,selectedParisiItoState β 0 hβ μ r ω)-
      parisiPotential β μ (r,selectedParisiItoState β 0 hβ μ r ω)∂canonicalBrownianMeasure)-
    (∫ω,parisiPotential β (scalarClippedTrialMeasure s hs μ) (l,selectedParisiItoState β 0 hβ μ l ω)-
      parisiPotential β μ (l,selectedParisiItoState β 0 hβ μ l ω)∂canonicalBrownianMeasure)=
      ∫t in (l:ℝ)..(r:ℝ),∫ω,
        scalarClippingPotentialSource β μ (scalarClippedTrialMeasure s hs μ)
          (t,selectedParisiItoState β 0 hβ μ t.toNNReal ω)∂canonicalBrownianMeasure := by
  apply scalarPotentialDifference_interval_integral β hβ μ _
    (scalarSupportCDF β μ q hq.1.le) (fun t=>max s (scalarSupportCDF β μ q hq.1.le t))
    (continuous_scalarSupportCDF β hβ μ hmin q hq hsupp)
    (continuous_const.max (continuous_scalarSupportCDF β hβ μ hmin q hq hsupp)) q hq.1.le hq.2.le _ _ l r hlr hrq
  · intro t ht
    exact (scalarSupportCDF_eq_cdf β hβ μ hmin q hq hsupp t ⟨ht.1.le,ht.2⟩).symm
  · intro t ht
    change parisiCDF (scalarClippedTrialMeasure s hs μ) t=max s (scalarSupportCDF β μ q hq.1.le t)
    rw [scalarClippedTrialMeasure_cdf s hs μ t ⟨ht.1.le,ht.2.le.trans hq.2.le⟩,
      scalarSupportCDF_eq_cdf β hβ μ hmin q hq hsupp t ⟨ht.1.le,ht.2⟩]

theorem scalarClipped_square_terminal_zero (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (T : ℝ≥0) (hT : (T:ℝ)≤1)
    (hfloor : s≤parisiCDF μ T) :
    scalarSquareDifferenceMoment β hβ μ (scalarClippedTrialMeasure s hs μ) T=0 := by
  unfold scalarSquareDifferenceMoment
  have he (x : ℝ) : scalarGradientDifference β μ (scalarClippedTrialMeasure s hs μ) (T,x)=0 := by
    have hh:=scalarClippedTrialMeasure_spatialField_terminal s hs β hβ μ T ⟨T.coe_nonneg,hT⟩ hfloor 1 x
    simpa only [parisiSpatialField_one,scalarGradientDifference,sub_eq_zero] using hh
  simp only [he,pow_two,mul_zero,integral_zero]

end QuantitativeFollowup
