module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingApproximation
public import Paper.ParisiCDFIntegral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Mark integrals are pulled back to one fixed genuine free measure.
The quantizer retains prescribed atoms and eventually retains every
order relation, including equal-variable diagonals. Thus dominated
convergence applies even when the original profile has atoms. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1000000

theorem nativeStreaming_round_lt_eventually (S : Finset Paper.Overlap)
    (r t : Paper.Overlap) :
    ∀ᶠN in atTop, (FRSB.preservingRound S N r<FRSB.preservingRound S N t ↔ r<t) := by
  by_cases he:r=t
  · subst t
    exact Eventually.of_forall (fun _=>by simp)
  · rcases lt_or_gt_of_ne he with hlt|hgt
    · exact ((FRSB.tendsto_preservingRound S r).eventually_lt
        (FRSB.tendsto_preservingRound S t) hlt).mono fun N hN=>by simp [hN,hlt]
    · exact ((FRSB.tendsto_preservingRound S t).eventually_lt
        (FRSB.tendsto_preservingRound S r) hgt).mono fun N hN=>by
        simp [not_lt_of_gt hN,not_lt_of_gt hgt]

theorem nativeStreaming_round_le_eventually (S : Finset Paper.Overlap)
    (r t : Paper.Overlap) :
    ∀ᶠN in atTop, (FRSB.preservingRound S N r≤FRSB.preservingRound S N t ↔ r≤t) := by
  exact (nativeStreaming_round_lt_eventually S t r).mono fun _ h=>by
    simpa only [not_lt] using not_congr h

theorem nativeStreaming_round_eq_eventually (S : Finset Paper.Overlap)
    (r t : Paper.Overlap) :
    ∀ᶠN in atTop, (FRSB.preservingRound S N r=FRSB.preservingRound S N t ↔ r=t) := by
  filter_upwards [nativeStreaming_round_le_eventually S r t,
    nativeStreaming_round_le_eventually S t r] with N hrt htr
  simp only [le_antisymm_iff,hrt,htr]

/-- Right CDF convergence at the actual moving rounded level retains
the diagonal atom, without a continuity-point assumption. -/
theorem nativeStreaming_preserving_cdf_at_round_tendsto (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (q : Paper.Overlap) :
    Tendsto (fun N=>Paper.parisiCDF (FRSB.preservingMeasure μ S N)
      (FRSB.preservingRound S N q)) atTop (𝓝 (Paper.parisiCDF μ q)) := by
  have he (N:ℕ) : Paper.parisiCDF (FRSB.preservingMeasure μ S N)
      (FRSB.preservingRound S N q)=
      ∫r : Paper.Overlap,if FRSB.preservingRound S N r≤FRSB.preservingRound S N q
        then (1:ℝ) else 0 ∂(μ:Measure Paper.Overlap) := by
    rw [Paper.parisiCDF_eq_integral_upperIndicator]
    change (∫r : Paper.Overlap,if (r:ℝ)≤(FRSB.preservingRound S N q:ℝ)
      then (1:ℝ) else 0 ∂(μ:Measure Paper.Overlap).map (FRSB.preservingRound S N))=_
    rw [integral_map (FRSB.measurable_preservingRound S N).aemeasurable
      ((measurable_const.ite ((isClosed_le continuous_subtype_val continuous_const).measurableSet)
        measurable_const).aestronglyMeasurable)]
    rfl
  simp_rw [he]
  rw [Paper.parisiCDF_eq_integral_upperIndicator]
  apply tendsto_integral_of_dominated_convergence (fun _=>(1:ℝ))
  · intro N
    exact (measurable_const.ite
      (measurableSet_le (FRSB.measurable_preservingRound S N) measurable_const)
      measurable_const).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    exact Eventually.of_forall fun r=>by split_ifs <;> norm_num
  · exact Eventually.of_forall fun r=>by
      apply Tendsto.congr' _ tendsto_const_nhds
      exact (nativeStreaming_round_le_eventually S r q).mono fun N h=>by
        dsimp only
        simp only [h,Subtype.coe_le_coe]

theorem nativeStreaming_free_integral_tendsto (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (F : ℕ→Paper.Overlap→ℝ) (f : Paper.Overlap→ℝ)
    (hF : ∀N,Measurable (F N)) (C : ℝ) (hC : 0≤C)
    (hb : ∀N r,|F N r|≤C)
    (hlim : ∀r,Tendsto (fun N=>F N (FRSB.preservingRound S N r)) atTop (𝓝 (f r))) :
    Tendsto (fun N=>∫r,F N r ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a)
      atTop (𝓝 (∫r,f r ∂parisiFreeMeasure μ a)) := by
  simp_rw [nativeStreaming_integral_free_preserving μ S hzero a ha hμ _ _ (hF _)]
  apply tendsto_integral_of_dominated_convergence (fun _=>C)
  · intro N
    exact ((hF N).comp (FRSB.measurable_preservingRound S N)).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    exact Eventually.of_forall fun r=>by simpa only [Real.norm_eq_abs] using hb N _
  · exact Eventually.of_forall hlim

theorem nativeStreaming_free_pair_integral_tendsto (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (F : ℕ→Paper.Overlap×Paper.Overlap→ℝ) (f : Paper.Overlap×Paper.Overlap→ℝ)
    (hF : ∀N,Measurable (F N)) (C : ℝ) (hC : 0≤C)
    (hb : ∀N z,|F N z|≤C)
    (hlim : ∀r t,Tendsto (fun N=>F N
      (FRSB.preservingRound S N r,FRSB.preservingRound S N t)) atTop (𝓝 (f (r,t)))) :
    Tendsto (fun N=>∫z,F N z ∂(parisiFreeMeasure (FRSB.preservingMeasure μ S N) a).prod
      (parisiFreeMeasure (FRSB.preservingMeasure μ S N) a)) atTop
      (𝓝 (∫z,f z ∂(parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a))) := by
  have he (N:ℕ) :
      (∫z,F N z ∂(parisiFreeMeasure (FRSB.preservingMeasure μ S N) a).prod
        (parisiFreeMeasure (FRSB.preservingMeasure μ S N) a))=
      ∫z,F N (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2)
        ∂(parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a) := by
    rw [←nativeStreaming_free_preserving_map μ S hzero a ha hμ N,
      Measure.map_prod_map _ _ (FRSB.measurable_preservingRound S N)
        (FRSB.measurable_preservingRound S N)]
    exact integral_map ((FRSB.measurable_preservingRound S N).prodMap
      (FRSB.measurable_preservingRound S N)).aemeasurable (hF N).aestronglyMeasurable
  simp_rw [he]
  apply tendsto_integral_of_dominated_convergence (fun _=>C)
  · intro N
    exact ((hF N).comp ((FRSB.measurable_preservingRound S N).prodMap
      (FRSB.measurable_preservingRound S N))).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    exact Eventually.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hb N _
  · exact Eventually.of_forall fun z=>hlim z.1 z.2

end QuantitativeFollowup
