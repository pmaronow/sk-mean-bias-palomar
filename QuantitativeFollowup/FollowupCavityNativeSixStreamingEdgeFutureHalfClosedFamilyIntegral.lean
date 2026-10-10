module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeFutureHalfClosedFamilyMoments

@[expose] public section

/-! Strict-future mark integrals use the original product free measure.
The actual shared-future tree law and every order boundary are retained
under profile rounding; equal-time diagonal atoms are masked genuinely while the incoming upper atoms remain. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem nativeStreamingEdgeFutureFamilyHalfClosedMoment_abs_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (j : ℕ)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (C : ℝ) (hC : 0≤C) (hG : ∀z σ,|G z σ|≤C) (z : Paper.Overlap×Paper.Overlap) :
    |nativeStreamingEdgeFutureFamilyHalfClosedMoment D μ a q T e j S G z|≤C := by
  classical
  unfold nativeStreamingEdgeFutureFamilyHalfClosedMoment
  split_ifs
  · exact nativeStreamingTerminalMarkMoment_abs_le_bound _ (G z) C (hG z)
  · simpa only [abs_zero] using hC

theorem nativeStreamingEdgeFutureFamilyHalfClosedMoment_preserving_tendsto
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (j : ℕ) (S : Finset Paper.Overlap)
    (heroot : q (e.depth+1)∈S) (hechild : q e.depth∈S)
    (hfroot : q (j+1)∈S) (hfchild : q j∈S)
    (GN : ℕ→Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hG : ∀z σ,Tendsto (fun N=>GN N
      (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2) σ) atTop (𝓝 (G z σ)))
    (z : Paper.Overlap×Paper.Overlap) :
    Tendsto (fun N=>nativeStreamingEdgeFutureFamilyHalfClosedMoment D (FRSB.preservingMeasure μ S N)
      a q T e j S (GN N) (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2)) atTop
        (𝓝 (nativeStreamingEdgeFutureFamilyHalfClosedMoment D μ a q T e j S G z)) := by
  classical
  have hm : ∀ᶠN in atTop,
      nativeStreamingEdgeFutureHalfClosedCondition q e j S
        (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2) ↔
          nativeStreamingEdgeFutureHalfClosedCondition q e j S z := by
    exact (nativeStreaming_round_lt_eventually S z.1 z.2).mono fun N hN=>by
      simp only [nativeStreamingEdgeFutureHalfClosedCondition,
        FRSB.preservingRound_gt_iff S N z.1 _ heroot,
        FRSB.preservingRound_le_iff S N z.1 _ hechild,
        FRSB.preservingRound_gt_iff S N z.2 _ hfroot,
        FRSB.preservingRound_le_iff S N z.2 _ hfchild,
        hN]
  by_cases hz : nativeStreamingEdgeFutureHalfClosedCondition q e j S z
  · have hp := tendsto_nativeStreamingEdgeFutureProbability_preserving D μ S a q hq T e j
      z.1 z.2 heroot hechild hfroot hfchild
      ⟨hz.1.1.le,hz.1.2⟩ ⟨hz.2.1.1.le,hz.2.1.2⟩
    have ht := tendsto_nativeStreamingMovingTerminalMarkMoment hp
      (fun N=>GN N (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2)) (G z) (hG z)
    apply Tendsto.congr' _ (by simpa only [nativeStreamingEdgeFutureFamilyHalfClosedMoment,hz,
      ite_true] using ht)
    exact hm.mono fun N hN=>by
      simp only [nativeStreamingEdgeFutureFamilyHalfClosedMoment,hN,hz,ite_true]
  · apply Tendsto.congr' _ (by
      simpa only [nativeStreamingEdgeFutureFamilyHalfClosedMoment,hz,ite_false] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0)))
    exact hm.mono fun N hN=>by
      simp only [nativeStreamingEdgeFutureFamilyHalfClosedMoment,hN,hz,ite_false]

theorem tendsto_nativeStreamingEdgeFutureFamilyHalfClosedFreeIntegral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (j : ℕ) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (heroot : q (e.depth+1)∈S) (hechild : q e.depth∈S)
    (hfroot : q (j+1)∈S) (hfchild : q j∈S)
    (GN : ℕ→Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hGN : ∀N σ,Continuous (fun z=>GN N z σ))
    (hG : ∀z σ,Tendsto (fun N=>GN N
      (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2) σ) atTop (𝓝 (G z σ)))
    (C : ℝ) (hC : 0≤C) (hbound : ∀N z σ,|GN N z σ|≤C) :
    Tendsto (fun N=>∫z,nativeStreamingEdgeFutureFamilyHalfClosedMoment D (FRSB.preservingMeasure μ S N)
      a q T e j S (GN N) z ∂(parisiFreeMeasure (FRSB.preservingMeasure μ S N) a).prod
        (parisiFreeMeasure (FRSB.preservingMeasure μ S N) a)) atTop
      (𝓝 (∫z,nativeStreamingEdgeFutureFamilyHalfClosedMoment D μ a q T e j S G z
        ∂(parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a))) :=
  nativeStreaming_free_pair_integral_tendsto μ S hzero a ha hμ _ _
    (fun N=>measurable_nativeStreamingEdgeFutureFamilyHalfClosedMoment D _ a q hq T e j S
      (GN N) (hGN N)) C hC
    (fun N z=>nativeStreamingEdgeFutureFamilyHalfClosedMoment_abs_le D _ a q T e j S
      (GN N) C hC (hbound N) z)
    (fun r l=>nativeStreamingEdgeFutureFamilyHalfClosedMoment_preserving_tendsto D μ a q hq T e j S
      heroot hechild hfroot hfchild GN G hG (r,l))


theorem nativeStreamingEdgeFutureFamilyHalfClosedIntegral_eq_Ioc
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (j : ℕ) (S : Finset Paper.Overlap)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hG : ∀σ,Continuous (fun z=>G z σ))
    (C : ℝ) (hC : 0≤C) (hbound : ∀z σ,|G z σ|≤C) :
    (∫z,nativeStreamingEdgeFutureFamilyHalfClosedMoment D μ a q T e j S G z
      ∂(parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) =
      ∫r in Ioc (q (e.depth+1)) (q e.depth),
        ∫l in Ioc (q (j+1)) (q j), if r<l then
          nativeStreamingTerminalMarkMoment
            (nativeStreamingEdgeFutureProbability D μ a q T e j r l) (G (r,l))
          else 0 ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a := by
  have hi : Integrable (nativeStreamingEdgeFutureFamilyHalfClosedMoment D μ a q T e j S G)
      ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) :=
    (integrable_const C).mono'
      (measurable_nativeStreamingEdgeFutureFamilyHalfClosedMoment D μ a q hq T e j S G hG).aestronglyMeasurable
      (.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using
          nativeStreamingEdgeFutureFamilyHalfClosedMoment_abs_le D μ a q T e j S G C hC hbound z)
  rw [integral_prod _ hi, ←integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall fun r => by
    by_cases hr : r∈Ioc (q (e.depth+1)) (q e.depth)
    · have hr' : q (e.depth+1)<r ∧ r≤q e.depth := hr
      rw [Set.indicator_of_mem hr, ←integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      exact .of_forall fun l => by
        simp only [nativeStreamingEdgeFutureFamilyHalfClosedMoment,
          nativeStreamingEdgeFutureHalfClosedCondition, hr', true_and,
          Set.indicator, mem_Ioc, ite_and]
    · have hr' : ¬(q (e.depth+1)<r ∧ r≤q e.depth) := hr
      rw [Set.indicator_of_notMem hr]
      simp only [nativeStreamingEdgeFutureFamilyHalfClosedMoment,
        nativeStreamingEdgeFutureHalfClosedCondition, hr', false_and, ite_false,
        integral_zero]

end QuantitativeFollowup
