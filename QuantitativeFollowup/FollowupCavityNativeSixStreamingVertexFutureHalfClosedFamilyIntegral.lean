module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingVertexFutureFamilyIntegral

@[expose] public section
/-! A genuine shared-future pair attached above a retained vertex.  The
halfclosed cell retains upper and interior profile atoms
while moving finite-spin tests pass to the actual free measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def nativeStreamingVertexFutureHalfClosedCondition (q : ℕ → Paper.Overlap)
    {T : FiniteTerminalGenealogy J} (v : FiniteCascadeRecordVertex T) (j : ℕ)
    (S : Finset Paper.Overlap) (r : Paper.Overlap) : Prop :=
  q (j+1)<r ∧ r≤q j ∧ q v.depth<r

theorem measurableSet_nativeStreamingVertexFutureHalfClosedCondition (q : ℕ → Paper.Overlap)
    {T : FiniteTerminalGenealogy J} (v : FiniteCascadeRecordVertex T) (j : ℕ)
    (S : Finset Paper.Overlap) :
    MeasurableSet {r | nativeStreamingVertexFutureHalfClosedCondition q v j S r} := by
  convert (measurableSet_Ioc : MeasurableSet (Ioc (q (j+1)) (q j))).inter
    (isOpen_Ioi.measurableSet : MeasurableSet (Ioi (q v.depth))) using 1
  ext r
  simp only [nativeStreamingVertexFutureHalfClosedCondition, mem_setOf_eq,
    mem_inter_iff, mem_Ioc, mem_Ioi, and_assoc]

def nativeStreamingVertexFutureFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) (j : ℕ)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ) (r : Paper.Overlap) : ℝ := by
  classical
  exact if nativeStreamingVertexFutureHalfClosedCondition q v j S r then
    nativeStreamingTerminalMarkMoment
      (nativeStreamingInsertedFuturePairProbability D μ a q T v j r) (G r) else 0

theorem measurable_nativeStreamingVertexFutureFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) (j : ℕ)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun r => G r σ)) :
    Measurable (nativeStreamingVertexFutureFamilyHalfClosedMoment D μ a q T v j S G) := by
  classical
  have hc := continuousOn_nativeStreamingVertexFutureFamilyMoment D μ a q hq T v j G hG
  have hsub : {r | nativeStreamingVertexFutureHalfClosedCondition q v j S r} ⊆
      Icc (q (j+1)) (q j) := fun r hr => ⟨hr.1.le,hr.2.1⟩
  convert (hc.mono hsub).measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
    (measurableSet_nativeStreamingVertexFutureHalfClosedCondition q v j S) using 1
  funext r
  by_cases hr : nativeStreamingVertexFutureHalfClosedCondition q v j S r <;>
    simp only [nativeStreamingVertexFutureFamilyHalfClosedMoment, Set.piecewise,
      Set.mem_setOf_eq, hr, ite_true, ite_false]

theorem nativeStreamingVertexFutureFamilyHalfClosedMoment_abs_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) (j : ℕ)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hG : ∀r σ, |G r σ| ≤ C) (r : Paper.Overlap) :
    |nativeStreamingVertexFutureFamilyHalfClosedMoment D μ a q T v j S G r| ≤ C := by
  classical
  unfold nativeStreamingVertexFutureFamilyHalfClosedMoment
  split_ifs
  · simpa only [nativeStreamingTerminalMarkMoment, Real.norm_eq_abs, probReal_univ,
      mul_one] using norm_integral_le_of_norm_le_const
      (μ := (nativeStreamingInsertedFuturePairProbability D μ a q T v j r :
        Measure ((AnisotropicObservationState n ×
          Records (AnisotropicObservationState n) (Configuration n) T) ×
            (Configuration n × Configuration n))))
      (f := fun z => G r (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
      (C := C)
      (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hG r
          (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
  · simpa only [abs_zero] using hC

theorem nativeStreamingVertexFutureFamilyHalfClosedMoment_preserving_tendsto
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (j : ℕ) (S : Finset Paper.Overlap)
    (hlo : q (j+1) ∈ S) (hhi : q j ∈ S) (hv : q v.depth ∈ S)
    (GN : ℕ → Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (hG : ∀r σ, Tendsto (fun N => GN N (FRSB.preservingRound S N r) σ) atTop (𝓝 (G r σ)))
    (r : Paper.Overlap) :
    Tendsto (fun N => nativeStreamingVertexFutureFamilyHalfClosedMoment D
      (FRSB.preservingMeasure μ S N) a q T v j S (GN N) (FRSB.preservingRound S N r))
      atTop (𝓝 (nativeStreamingVertexFutureFamilyHalfClosedMoment D μ a q T v j S G r)) := by
  classical
  have hm (N : ℕ) : nativeStreamingVertexFutureHalfClosedCondition q v j S
      (FRSB.preservingRound S N r) ↔ nativeStreamingVertexFutureHalfClosedCondition q v j S r := by
    simp only [nativeStreamingVertexFutureHalfClosedCondition,
      FRSB.preservingRound_gt_iff S N r _ hlo,
      FRSB.preservingRound_le_iff S N r _ hhi,
      FRSB.preservingRound_gt_iff S N r _ hv]
  by_cases hr : nativeStreamingVertexFutureHalfClosedCondition q v j S r
  · have hp := tendsto_nativeStreamingInsertedFuturePairProbability D
      (FRSB.tendsto_preservingMeasure μ S) a q hq T v j
      (FRSB.tendsto_preservingRound S r)
      (fun N => by
        have hN := (hm N).mpr hr
        exact ⟨hN.1.le,hN.2.1⟩) ⟨hr.1.le,hr.2.1⟩
    have ht := tendsto_nativeStreamingMovingTerminalMarkMoment hp
      (fun N => GN N (FRSB.preservingRound S N r)) (G r) (hG r)
    apply Tendsto.congr' _ (by simpa only [nativeStreamingVertexFutureFamilyHalfClosedMoment,
      hr,ite_true] using ht)
    exact Eventually.of_forall fun N => by
      simp only [nativeStreamingVertexFutureFamilyHalfClosedMoment,hm N,hr,ite_true]
  · apply Tendsto.congr' _ (by
      simpa only [nativeStreamingVertexFutureFamilyHalfClosedMoment,hr,ite_false] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    exact Eventually.of_forall fun N => by
      simp only [nativeStreamingVertexFutureFamilyHalfClosedMoment,hm N,hr,ite_false]

theorem tendsto_nativeStreamingVertexFutureFamilyHalfClosedFreeIntegral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (j : ℕ) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (hlo : q (j+1)∈S) (hhi : q j∈S) (hv : q v.depth∈S)
    (GN : ℕ → Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (hGN : ∀N σ, Continuous (fun r => GN N r σ))
    (hG : ∀r σ, Tendsto (fun N => GN N (FRSB.preservingRound S N r) σ) atTop (𝓝 (G r σ)))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀N r σ, |GN N r σ| ≤ C) :
    Tendsto (fun N => ∫r, nativeStreamingVertexFutureFamilyHalfClosedMoment D
      (FRSB.preservingMeasure μ S N) a q T v j S (GN N) r
        ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a) atTop
      (𝓝 (∫r, nativeStreamingVertexFutureFamilyHalfClosedMoment D μ a q T v j S G r
        ∂parisiFreeMeasure μ a)) :=
  nativeStreaming_free_integral_tendsto μ S hzero a ha hμ _ _
    (fun N => measurable_nativeStreamingVertexFutureFamilyHalfClosedMoment D _ a q hq T v j S
      (GN N) (hGN N)) C hC
    (fun N r => nativeStreamingVertexFutureFamilyHalfClosedMoment_abs_le D _ a q T v j S
      (GN N) C hC (hbound N) r)
    (nativeStreamingVertexFutureFamilyHalfClosedMoment_preserving_tendsto D μ a q hq T v j S
      hlo hhi hv GN G hG)


theorem integral_nativeStreamingVertexFutureFamilyHalfClosedMoment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (j : ℕ) (S : Finset Paper.Overlap)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ) :
    (∫r, nativeStreamingVertexFutureFamilyHalfClosedMoment D μ a q T v j S G r
      ∂parisiFreeMeasure μ a) =
      ∫r in Ioc (q (j+1)) (q j), if q v.depth<r then
        nativeStreamingTerminalMarkMoment
          (nativeStreamingInsertedFuturePairProbability D μ a q T v j r) (G r)
        else 0 ∂parisiFreeMeasure μ a := by
  rw [←integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall fun r => by
    by_cases hr : r∈Ioc (q (j+1)) (q j)
    · have hr' : q (j+1)<r ∧ r≤q j := hr
      simp only [nativeStreamingVertexFutureFamilyHalfClosedMoment,
        nativeStreamingVertexFutureHalfClosedCondition, hr', true_and,
        Set.indicator_of_mem hr]
    · have hr' : ¬(q (j+1)<r ∧ r≤q j) := hr
      have hc : ¬nativeStreamingVertexFutureHalfClosedCondition q v j S r :=
        fun h => hr' ⟨h.1,h.2.1⟩
      simp only [nativeStreamingVertexFutureFamilyHalfClosedMoment,
        hc,
        Set.indicator_of_notMem hr, ite_false]

end QuantitativeFollowup
