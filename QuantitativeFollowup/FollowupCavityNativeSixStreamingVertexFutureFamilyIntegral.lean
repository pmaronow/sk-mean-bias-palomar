module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFuturePairContinuity
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMovingTerminalMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPreservingIntegrals

@[expose] public section

/-! A genuine shared-future pair attached above a retained vertex.  The
strict cell and prescribed-level mask keep every profile atom intact
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

def nativeStreamingVertexFutureOpenCondition (q : ℕ → Paper.Overlap)
    {T : FiniteTerminalGenealogy J} (v : FiniteCascadeRecordVertex T) (j : ℕ)
    (S : Finset Paper.Overlap) (r : Paper.Overlap) : Prop :=
  q (j+1)<r ∧ r<q j ∧ r∉S ∧ q v.depth<r

theorem measurableSet_nativeStreamingVertexFutureOpenCondition (q : ℕ → Paper.Overlap)
    {T : FiniteTerminalGenealogy J} (v : FiniteCascadeRecordVertex T) (j : ℕ)
    (S : Finset Paper.Overlap) :
    MeasurableSet {r | nativeStreamingVertexFutureOpenCondition q v j S r} :=
  isOpen_Ioi.measurableSet.inter (isOpen_Iio.measurableSet.inter
    (S.finite_toSet.measurableSet.compl.inter isOpen_Ioi.measurableSet))

def nativeStreamingVertexFutureFamilyMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) (j : ℕ)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ) (r : Paper.Overlap) : ℝ := by
  classical
  exact if nativeStreamingVertexFutureOpenCondition q v j S r then
    nativeStreamingTerminalMarkMoment
      (nativeStreamingInsertedFuturePairProbability D μ a q T v j r) (G r) else 0

theorem continuousOn_nativeStreamingVertexFutureFamilyMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) (j : ℕ)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun r => G r σ)) :
    ContinuousOn (fun r => nativeStreamingTerminalMarkMoment
      (nativeStreamingInsertedFuturePairProbability D μ a q T v j r) (G r))
        (Icc (q (j+1)) (q j)) := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_iff_continuousAt.mpr
  intro r
  apply tendsto_nativeStreamingMovingTerminalMarkMoment
    (tendsto_nativeStreamingInsertedFuturePairProbability D tendsto_const_nhds a q hq T v j
      (continuous_subtype_val.tendsto r) (fun x => x.2) r.2)
  exact fun σ => ((hG σ).comp continuous_subtype_val).tendsto r

theorem measurable_nativeStreamingVertexFutureFamilyMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) (j : ℕ)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun r => G r σ)) :
    Measurable (nativeStreamingVertexFutureFamilyMaskedMoment D μ a q T v j S G) := by
  classical
  have hc := continuousOn_nativeStreamingVertexFutureFamilyMoment D μ a q hq T v j G hG
  have hsub : {r | nativeStreamingVertexFutureOpenCondition q v j S r} ⊆
      Icc (q (j+1)) (q j) := fun r hr => ⟨hr.1.le,hr.2.1.le⟩
  convert (hc.mono hsub).measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
    (measurableSet_nativeStreamingVertexFutureOpenCondition q v j S) using 1
  funext r
  by_cases hr : nativeStreamingVertexFutureOpenCondition q v j S r <;>
    simp only [nativeStreamingVertexFutureFamilyMaskedMoment, Set.piecewise,
      Set.mem_setOf_eq, hr, ite_true, ite_false]

theorem nativeStreamingVertexFutureFamilyMaskedMoment_abs_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) (j : ℕ)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hG : ∀r σ, |G r σ| ≤ C) (r : Paper.Overlap) :
    |nativeStreamingVertexFutureFamilyMaskedMoment D μ a q T v j S G r| ≤ C := by
  classical
  unfold nativeStreamingVertexFutureFamilyMaskedMoment
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

theorem nativeStreamingVertexFutureFamilyMaskedMoment_preserving_tendsto
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
    Tendsto (fun N => nativeStreamingVertexFutureFamilyMaskedMoment D
      (FRSB.preservingMeasure μ S N) a q T v j S (GN N) (FRSB.preservingRound S N r))
      atTop (𝓝 (nativeStreamingVertexFutureFamilyMaskedMoment D μ a q T v j S G r)) := by
  classical
  have hm (N : ℕ) : nativeStreamingVertexFutureOpenCondition q v j S
      (FRSB.preservingRound S N r) ↔ nativeStreamingVertexFutureOpenCondition q v j S r := by
    simp only [nativeStreamingVertexFutureOpenCondition,
      FRSB.preservingRound_gt_iff S N r _ hlo,
      FRSB.preservingRound_lt_iff S N r _ hhi,
      nativeStreaming_round_mem_prescribed_iff,
      FRSB.preservingRound_gt_iff S N r _ hv]
  by_cases hr : nativeStreamingVertexFutureOpenCondition q v j S r
  · have hp := tendsto_nativeStreamingInsertedFuturePairProbability D
      (FRSB.tendsto_preservingMeasure μ S) a q hq T v j
      (FRSB.tendsto_preservingRound S r)
      (fun N => by
        have hN := (hm N).mpr hr
        exact ⟨hN.1.le,hN.2.1.le⟩) ⟨hr.1.le,hr.2.1.le⟩
    have ht := tendsto_nativeStreamingMovingTerminalMarkMoment hp
      (fun N => GN N (FRSB.preservingRound S N r)) (G r) (hG r)
    apply Tendsto.congr' _ (by simpa only [nativeStreamingVertexFutureFamilyMaskedMoment,
      hr,ite_true] using ht)
    exact Eventually.of_forall fun N => by
      simp only [nativeStreamingVertexFutureFamilyMaskedMoment,hm N,hr,ite_true]
  · apply Tendsto.congr' _ (by
      simpa only [nativeStreamingVertexFutureFamilyMaskedMoment,hr,ite_false] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    exact Eventually.of_forall fun N => by
      simp only [nativeStreamingVertexFutureFamilyMaskedMoment,hm N,hr,ite_false]

theorem tendsto_nativeStreamingVertexFutureFamilyFreeIntegral (D : AnisotropicSpinModel n)
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
    Tendsto (fun N => ∫r, nativeStreamingVertexFutureFamilyMaskedMoment D
      (FRSB.preservingMeasure μ S N) a q T v j S (GN N) r
        ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a) atTop
      (𝓝 (∫r, nativeStreamingVertexFutureFamilyMaskedMoment D μ a q T v j S G r
        ∂parisiFreeMeasure μ a)) :=
  nativeStreaming_free_integral_tendsto μ S hzero a ha hμ _ _
    (fun N => measurable_nativeStreamingVertexFutureFamilyMaskedMoment D _ a q hq T v j S
      (GN N) (hGN N)) C hC
    (fun N r => nativeStreamingVertexFutureFamilyMaskedMoment_abs_le D _ a q T v j S
      (GN N) C hC (hbound N) r)
    (nativeStreamingVertexFutureFamilyMaskedMoment_preserving_tendsto D μ a q hq T v j S
      hlo hhi hv GN G hG)

end QuantitativeFollowup
