module
public import QuantitativeFollowup.VectorQuantileSetVariance
public import FourPapersCommon.TwoSidedSquareComparison

@[expose] public section

/-! Actual pointwise-in-level second-moment bound from adjacent averaging
kernels. This is the probabilistic estimate used in the level-bin argument;
the final geometric/layer-cake quantile-interval estimate is separate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorCenteredSelfOverlap_square_le_two_kernel_variances (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s β t : ℝ) (hβ : β≠0) (ht : t<1)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (κp κm : Paper.Overlap→ℝ) (hκp : Measurable κp) (hκm : Measurable κm)
    (hposp : ∀p,0≤κp p) (hposm : ∀p,0≤κm p)
    (hLp : MemLp κp 2 (parisiFreeMeasure μ s)) (hLm : MemLp κm 2 (parisiFreeMeasure μ s))
    (hnp : (∫p,κp p ∂parisiFreeMeasure μ s)=1) (hnm : (∫p,κm p ∂parisiFreeMeasure μ s)=1)
    (q : Paper.Overlap) (hSp : ∀ᵐp ∂parisiFreeMeasure μ s,κp p≠0→q≤p)
    (hSm : ∀ᵐp ∂parisiFreeMeasure μ s,κm p≠0→p≤q)
    (d : ℝ) (hd : 0≤d) (hdp : vectorKernelOverlapLevel μ s κp-(q:ℝ)≤d)
    (hdm : (q:ℝ)-vectorKernelOverlapLevel μ s κm≤d) :
    (∫z,vectorCenteredSelfOverlap (n:=n) μ β t ht.le q z^2 ∂vectorMeasureSpinPathLaw μ β t s ht.le)≤
      2*d^2+8*variance (vectorCenteredKernelScore (n:=n) μ s β t ht.le κp)
        (vectorMeasureSpinPathLaw μ β t s ht.le)+
      8*variance (vectorCenteredKernelScore (n:=n) μ s β t ht.le κm)
        (vectorMeasureSpinPathLaw μ β t s ht.le) := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t s ht.le
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t s ht.le
  have hip:=hLp.integrable one_le_two
  have him:=hLm.integrable one_le_two
  have hp:=vectorCenteredKernelScore_future_comparison hn μ s β t s hβ ht κp hκp hip hposp hnp q hSp
  have hm:=vectorCenteredKernelScore_past_lower_comparison (n:=n) μ s β t s hβ ht κm hκm him hposm hnm q hSm
  have hp' : vectorCenteredSelfOverlap μ β t ht.le q≤ᵐ[J]fun z=>d+
      2*(J[vectorCenteredKernelScore μ s β t ht.le κp|vectorSpinPast n (q:ℝ).toNNReal] z):=
    hp.mono fun z hz=>hz.trans (add_le_add hdp le_rfl)
  have hm' : (fun z=>-d+2*(J[vectorCenteredKernelScore μ s β t ht.le κm|
      vectorSpinPast n (q:ℝ).toNNReal] z))≤ᵐ[J]vectorCenteredSelfOverlap μ β t ht.le q:=
    hm.mono fun z hz=>by
      apply le_trans _ hz
      exact add_le_add (by linarith) le_rfl
  have h:=integral_square_le_of_two_sided_comparison J _ _ _
    (memLp_vectorCenteredSelfOverlap hn μ β t s ht.le q)
    ((memLp_vectorCenteredKernelScore_normalized μ s β t s ht.le κp hκp hip hposp hnp).condExp one_le_two)
    ((memLp_vectorCenteredKernelScore_normalized μ s β t s ht.le κm hκm him hposm hnm).condExp one_le_two)
    d hd hp' hm'
  have hvp:=(vectorCenteredKernelScore_conditional_square_variance hn μ s β t hβ ht hs hμ hmin
    κp hκp hposp hLp hnp q).1
  have hvm:=(vectorCenteredKernelScore_conditional_square_variance hn μ s β t hβ ht hs hμ hmin
    κm hκm hposm hLm hnm q).1
  exact h.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hvp (by norm_num)))
    (mul_le_mul_of_nonneg_left hvm (by norm_num)))

end QuantitativeFollowup
