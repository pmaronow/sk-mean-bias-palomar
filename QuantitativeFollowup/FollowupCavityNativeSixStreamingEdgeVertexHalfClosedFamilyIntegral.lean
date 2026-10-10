module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeVertexFamilyIntegral
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeVertexPairContinuity
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMovingTerminalMoments

@[expose] public section

/-! Actual vertex--edge cross expectations retain every endpoint and
interior atom of the halfclosed incoming edge. The two conditional terminal
draws and the entire old record pass under preserving weak approximation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def nativeStreamingEdgeVertexFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (r : Paper.Overlap) : ℝ :=
  if q (e.depth+1)<r ∧ r≤q e.depth then
    nativeStreamingTerminalMarkMoment (nativeStreamingEdgeVertexPairProbability D μ a q T e v r)
      (G r) else 0

theorem measurable_nativeStreamingEdgeVertexFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun r => G r σ)) :
    Measurable (nativeStreamingEdgeVertexFamilyHalfClosedMoment D μ a q T e v G) := by
  classical
  have hc := continuousOn_nativeStreamingEdgeVertexFamilyMoment D μ a q hq T e v G hG
  have hs : MeasurableSet {r : Paper.Overlap | q (e.depth+1)<r ∧ r≤q e.depth} :=
    measurableSet_Ioc
  convert (hc.mono (fun r hr => ⟨hr.1.le,hr.2⟩)).measurable_piecewise
    (g:=fun _ => (0:ℝ)) continuousOn_const hs using 1
  funext r
  by_cases hr : q (e.depth+1)<r ∧ r≤q e.depth <;>
    simp [nativeStreamingEdgeVertexFamilyHalfClosedMoment,Set.piecewise,hr]

theorem nativeStreamingEdgeVertexFamilyHalfClosedMoment_abs_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (C : ℝ) (hC : 0≤C) (hG : ∀r σ, |G r σ|≤C) (r : Paper.Overlap) :
    |nativeStreamingEdgeVertexFamilyHalfClosedMoment D μ a q T e v G r|≤C := by
  classical
  unfold nativeStreamingEdgeVertexFamilyHalfClosedMoment
  split_ifs
  · simpa only [nativeStreamingTerminalMarkMoment,Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const
        (μ:=(nativeStreamingEdgeVertexPairProbability D μ a q T e v r :
          Measure ((AnisotropicObservationState n × Records (AnisotropicObservationState n)
            (Configuration n) T) × (Configuration n × Configuration n))))
        (f := fun z => G r (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
        (C := C)
        (Eventually.of_forall fun z => by
          simpa only [Real.norm_eq_abs] using
            hG r (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
  · simpa only [abs_zero] using hC

theorem nativeStreamingEdgeVertexFamilyHalfClosedMoment_preserving_tendsto
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T) (S : Finset Paper.Overlap)
    (hlo : q (e.depth+1)∈S) (hhi : q e.depth∈S)
    (GN : ℕ → Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (hG : ∀r σ, Tendsto (fun N => GN N (FRSB.preservingRound S N r) σ) atTop (𝓝 (G r σ)))
    (r : Paper.Overlap) :
    Tendsto (fun N => nativeStreamingEdgeVertexFamilyHalfClosedMoment D
      (FRSB.preservingMeasure μ S N) a q T e v (GN N) (FRSB.preservingRound S N r))
        atTop (𝓝 (nativeStreamingEdgeVertexFamilyHalfClosedMoment D μ a q T e v G r)) := by
  classical
  have hm (N : ℕ) :
      (q (e.depth+1)<FRSB.preservingRound S N r ∧
        FRSB.preservingRound S N r≤q e.depth) ↔
      (q (e.depth+1)<r ∧ r≤q e.depth) := by
    simp only [FRSB.preservingRound_gt_iff S N r _ hlo,
      FRSB.preservingRound_le_iff S N r _ hhi]
  by_cases hr : q (e.depth+1)<r ∧ r≤q e.depth
  · have hp := tendsto_nativeStreamingEdgeVertexPairProbability D
      (FRSB.tendsto_preservingMeasure μ S) a q hq T e v (FRSB.tendsto_preservingRound S r)
      (fun N => ⟨((hm N).mpr hr).1.le,((hm N).mpr hr).2⟩)
      ⟨hr.1.le,hr.2⟩
    simpa [nativeStreamingEdgeVertexFamilyHalfClosedMoment,hm,hr] using
      tendsto_nativeStreamingMovingTerminalMarkMoment hp
        (fun N => GN N (FRSB.preservingRound S N r)) (G r) (hG r)
  · simpa [nativeStreamingEdgeVertexFamilyHalfClosedMoment,hm,hr] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

theorem tendsto_nativeStreamingEdgeVertexFamilyHalfClosedFreeIntegral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (hlo : q (e.depth+1)∈S) (hhi : q e.depth∈S)
    (GN : ℕ → Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (hGN : ∀N σ, Continuous (fun r => GN N r σ))
    (hG : ∀r σ, Tendsto (fun N => GN N (FRSB.preservingRound S N r) σ) atTop (𝓝 (G r σ)))
    (C : ℝ) (hC : 0≤C) (hbound : ∀N r σ, |GN N r σ|≤C) :
    Tendsto (fun N => ∫r, nativeStreamingEdgeVertexFamilyHalfClosedMoment D
      (FRSB.preservingMeasure μ S N) a q T e v (GN N) r
        ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a) atTop
      (𝓝 (∫r, nativeStreamingEdgeVertexFamilyHalfClosedMoment D μ a q T e v G r
        ∂parisiFreeMeasure μ a)) :=
  nativeStreaming_free_integral_tendsto μ S hzero a ha hμ _ _
    (fun N => measurable_nativeStreamingEdgeVertexFamilyHalfClosedMoment D _ a q hq T e v
      (GN N) (hGN N)) C hC
    (fun N r => nativeStreamingEdgeVertexFamilyHalfClosedMoment_abs_le D _ a q T e v
      (GN N) C hC (hbound N) r)
    (nativeStreamingEdgeVertexFamilyHalfClosedMoment_preserving_tendsto D μ a q hq T e v S
      hlo hhi GN G hG)


theorem integral_nativeStreamingEdgeVertexFamilyHalfClosedMoment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ) :
    (∫r, nativeStreamingEdgeVertexFamilyHalfClosedMoment D μ a q T e v G r
      ∂parisiFreeMeasure μ a) =
    ∫r in Ioc (q (e.depth+1)) (q e.depth), nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgeVertexPairProbability D μ a q T e v r) (G r)
      ∂parisiFreeMeasure μ a := by
  rw [←integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall fun r => by
    simp only [nativeStreamingEdgeVertexFamilyHalfClosedMoment, Set.indicator, mem_Ioc]


end QuantitativeFollowup
