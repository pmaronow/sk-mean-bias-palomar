module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSingleFamilyIntegral
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeCurrentCDFIntegral

@[expose] public section

/-! Halfclosed Stieltjes edge integrals retain the upper endpoint atom
and every prescribed interior atom.  The exact quantizer preserves
these masks before the actual marked-law limit is integrated. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def nativeStreamingEdgeSingleFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × Configuration n → ℝ)
    (r : Paper.Overlap) : ℝ :=
  if q (e.depth+1)<r ∧ r≤q e.depth then
    nativeStreamingTerminalMarkMoment (nativeStreamingEdgeSingleMarkProbability D μ a q T e r)
      (G r) else 0

theorem measurable_nativeStreamingEdgeSingleFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × Configuration n → ℝ)
    (hG : ∀σ, Continuous (fun r => G r σ)) :
    Measurable (nativeStreamingEdgeSingleFamilyHalfClosedMoment D μ a q T e G) := by
  classical
  have hc := continuousOn_nativeStreamingEdgeSingleFamilyMoment D μ a q hq T e G hG
  have hs : MeasurableSet {r : Paper.Overlap | q (e.depth+1)<r ∧ r≤q e.depth} :=
    measurableSet_Ioc
  convert (hc.mono (fun r hr => ⟨hr.1.le,hr.2⟩)).measurable_piecewise
    (g:=fun _ => (0:ℝ)) continuousOn_const hs using 1
  funext r
  by_cases hr : q (e.depth+1)<r ∧ r≤q e.depth <;>
    simp [nativeStreamingEdgeSingleFamilyHalfClosedMoment,Set.piecewise,hr]

theorem nativeStreamingEdgeSingleFamilyHalfClosedMoment_abs_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × Configuration n → ℝ)
    (C : ℝ) (hC : 0≤C) (hG : ∀r σ, |G r σ|≤C) (r : Paper.Overlap) :
    |nativeStreamingEdgeSingleFamilyHalfClosedMoment D μ a q T e G r|≤C := by
  classical
  unfold nativeStreamingEdgeSingleFamilyHalfClosedMoment
  split_ifs
  · simpa only [nativeStreamingTerminalMarkMoment,Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const
        (μ:=(nativeStreamingEdgeSingleMarkProbability D μ a q T e r :
          Measure ((AnisotropicObservationState n × Records (AnisotropicObservationState n)
            (Configuration n) T) × Configuration n)))
        (f := fun z => G r (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
        (C := C)
        (Eventually.of_forall fun z => by
          simpa only [Real.norm_eq_abs] using
            hG r (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
  · simpa only [abs_zero] using hC

theorem nativeStreamingEdgeSingleFamilyHalfClosedMoment_preserving_tendsto
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (S : Finset Paper.Overlap)
    (hlo : q (e.depth+1)∈S) (hhi : q e.depth∈S)
    (GN : ℕ → Paper.Overlap → TerminalSpins (Configuration n) T × Configuration n → ℝ)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × Configuration n → ℝ)
    (hG : ∀r σ, Tendsto (fun N => GN N (FRSB.preservingRound S N r) σ) atTop (𝓝 (G r σ)))
    (r : Paper.Overlap) :
    Tendsto (fun N => nativeStreamingEdgeSingleFamilyHalfClosedMoment D
      (FRSB.preservingMeasure μ S N) a q T e (GN N) (FRSB.preservingRound S N r))
        atTop (𝓝 (nativeStreamingEdgeSingleFamilyHalfClosedMoment D μ a q T e G r)) := by
  classical
  have hm (N : ℕ) :
      (q (e.depth+1)<FRSB.preservingRound S N r ∧
        FRSB.preservingRound S N r≤q e.depth) ↔
      (q (e.depth+1)<r ∧ r≤q e.depth) := by
    simp only [FRSB.preservingRound_gt_iff S N r _ hlo,
      FRSB.preservingRound_le_iff S N r _ hhi]
  by_cases hr : q (e.depth+1)<r ∧ r≤q e.depth
  · have hp := tendsto_nativeStreamingEdgeSingleMarkProbability D
      (FRSB.tendsto_preservingMeasure μ S) a q hq T e (FRSB.tendsto_preservingRound S r)
      (fun N => ⟨((hm N).mpr hr).1.le,((hm N).mpr hr).2⟩)
      ⟨hr.1.le,hr.2⟩
    simpa [nativeStreamingEdgeSingleFamilyHalfClosedMoment,hm,hr] using
      tendsto_nativeStreamingMovingTerminalMarkMoment hp
        (fun N => GN N (FRSB.preservingRound S N r)) (G r) (hG r)
  · simpa [nativeStreamingEdgeSingleFamilyHalfClosedMoment,hm,hr] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

theorem tendsto_nativeStreamingEdgeSingleFamilyHalfClosedFreeIntegral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (hlo : q (e.depth+1)∈S) (hhi : q e.depth∈S)
    (GN : ℕ → Paper.Overlap → TerminalSpins (Configuration n) T × Configuration n → ℝ)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × Configuration n → ℝ)
    (hGN : ∀N σ, Continuous (fun r => GN N r σ))
    (hG : ∀r σ, Tendsto (fun N => GN N (FRSB.preservingRound S N r) σ) atTop (𝓝 (G r σ)))
    (C : ℝ) (hC : 0≤C) (hbound : ∀N r σ, |GN N r σ|≤C) :
    Tendsto (fun N => ∫r, nativeStreamingEdgeSingleFamilyHalfClosedMoment D
      (FRSB.preservingMeasure μ S N) a q T e (GN N) r
        ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a) atTop
      (𝓝 (∫r, nativeStreamingEdgeSingleFamilyHalfClosedMoment D μ a q T e G r
        ∂parisiFreeMeasure μ a)) :=
  nativeStreaming_free_integral_tendsto μ S hzero a ha hμ _ _
    (fun N => measurable_nativeStreamingEdgeSingleFamilyHalfClosedMoment D _ a q hq T e
      (GN N) (hGN N)) C hC
    (fun N r => nativeStreamingEdgeSingleFamilyHalfClosedMoment_abs_le D _ a q T e
      (GN N) C hC (hbound N) r)
    (nativeStreamingEdgeSingleFamilyHalfClosedMoment_preserving_tendsto D μ a q hq T e S
      hlo hhi GN G hG)


def nativeStreamingEdgeCurrentFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (r : Paper.Overlap) : ℝ :=
  if q (e.depth+1)<r ∧ r≤q e.depth then
    nativeStreamingTerminalMarkMoment (nativeStreamingEdgeCurrentPairProbability D μ a q T e r)
      (G r) else 0

theorem measurable_nativeStreamingEdgeCurrentFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun r => G r σ)) :
    Measurable (nativeStreamingEdgeCurrentFamilyHalfClosedMoment D μ a q T e G) := by
  classical
  have hc := continuousOn_nativeStreamingEdgeCurrentFamilyMoment D μ a q hq T e G hG
  have hs : MeasurableSet {r : Paper.Overlap | q (e.depth+1)<r ∧ r≤q e.depth} :=
    measurableSet_Ioc
  convert (hc.mono (fun r hr => ⟨hr.1.le,hr.2⟩)).measurable_piecewise
    (g:=fun _ => (0:ℝ)) continuousOn_const hs using 1
  funext r
  by_cases hr : q (e.depth+1)<r ∧ r≤q e.depth <;>
    simp [nativeStreamingEdgeCurrentFamilyHalfClosedMoment,Set.piecewise,hr]

theorem nativeStreamingEdgeCurrentFamilyHalfClosedMoment_abs_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (C : ℝ) (hC : 0≤C) (hG : ∀r σ, |G r σ|≤C) (r : Paper.Overlap) :
    |nativeStreamingEdgeCurrentFamilyHalfClosedMoment D μ a q T e G r|≤C := by
  classical
  unfold nativeStreamingEdgeCurrentFamilyHalfClosedMoment
  split_ifs
  · simpa only [nativeStreamingTerminalMarkMoment,Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const
        (μ:=(nativeStreamingEdgeCurrentPairProbability D μ a q T e r :
          Measure ((AnisotropicObservationState n × Records (AnisotropicObservationState n)
            (Configuration n) T) × (Configuration n × Configuration n))))
        (f := fun z => G r (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
        (C := C)
        (Eventually.of_forall fun z => by
          simpa only [Real.norm_eq_abs] using
            hG r (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
  · simpa only [abs_zero] using hC

theorem nativeStreamingEdgeCurrentFamilyHalfClosedMoment_preserving_tendsto
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (S : Finset Paper.Overlap)
    (hlo : q (e.depth+1)∈S) (hhi : q e.depth∈S)
    (GN : ℕ → Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (hG : ∀r σ, Tendsto (fun N => GN N (FRSB.preservingRound S N r) σ) atTop (𝓝 (G r σ)))
    (r : Paper.Overlap) :
    Tendsto (fun N => nativeStreamingEdgeCurrentFamilyHalfClosedMoment D
      (FRSB.preservingMeasure μ S N) a q T e (GN N) (FRSB.preservingRound S N r))
        atTop (𝓝 (nativeStreamingEdgeCurrentFamilyHalfClosedMoment D μ a q T e G r)) := by
  classical
  have hm (N : ℕ) :
      (q (e.depth+1)<FRSB.preservingRound S N r ∧
        FRSB.preservingRound S N r≤q e.depth) ↔
      (q (e.depth+1)<r ∧ r≤q e.depth) := by
    simp only [FRSB.preservingRound_gt_iff S N r _ hlo,
      FRSB.preservingRound_le_iff S N r _ hhi]
  by_cases hr : q (e.depth+1)<r ∧ r≤q e.depth
  · have hp := tendsto_nativeStreamingEdgeCurrentPairProbability D
      (FRSB.tendsto_preservingMeasure μ S) a q hq T e (FRSB.tendsto_preservingRound S r)
      (fun N => ⟨((hm N).mpr hr).1.le,((hm N).mpr hr).2⟩)
      ⟨hr.1.le,hr.2⟩
    simpa [nativeStreamingEdgeCurrentFamilyHalfClosedMoment,hm,hr] using
      tendsto_nativeStreamingMovingTerminalMarkMoment hp
        (fun N => GN N (FRSB.preservingRound S N r)) (G r) (hG r)
  · simpa [nativeStreamingEdgeCurrentFamilyHalfClosedMoment,hm,hr] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

theorem tendsto_nativeStreamingEdgeCurrentFamilyHalfClosedFreeIntegral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (hlo : q (e.depth+1)∈S) (hhi : q e.depth∈S)
    (GN : ℕ → Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (hGN : ∀N σ, Continuous (fun r => GN N r σ))
    (hG : ∀r σ, Tendsto (fun N => GN N (FRSB.preservingRound S N r) σ) atTop (𝓝 (G r σ)))
    (C : ℝ) (hC : 0≤C) (hbound : ∀N r σ, |GN N r σ|≤C) :
    Tendsto (fun N => ∫r, nativeStreamingEdgeCurrentFamilyHalfClosedMoment D
      (FRSB.preservingMeasure μ S N) a q T e (GN N) r
        ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a) atTop
      (𝓝 (∫r, nativeStreamingEdgeCurrentFamilyHalfClosedMoment D μ a q T e G r
        ∂parisiFreeMeasure μ a)) :=
  nativeStreaming_free_integral_tendsto μ S hzero a ha hμ _ _
    (fun N => measurable_nativeStreamingEdgeCurrentFamilyHalfClosedMoment D _ a q hq T e
      (GN N) (hGN N)) C hC
    (fun N r => nativeStreamingEdgeCurrentFamilyHalfClosedMoment_abs_le D _ a q T e
      (GN N) C hC (hbound N) r)
    (nativeStreamingEdgeCurrentFamilyHalfClosedMoment_preserving_tendsto D μ a q hq T e S
      hlo hhi GN G hG)


def nativeStreamingEdgeCurrentCDFHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ) (r : Paper.Overlap) : ℝ :=
  Paper.parisiCDF μ r * nativeStreamingEdgeCurrentFamilyHalfClosedMoment D μ a q T e G r

theorem measurable_nativeStreamingEdgeCurrentCDFHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun r => G r σ)) :
    Measurable (nativeStreamingEdgeCurrentCDFHalfClosedMoment D μ a q T e G) :=
  ((Paper.parisiCDF_measurable μ).comp measurable_subtype_coe).mul
    (measurable_nativeStreamingEdgeCurrentFamilyHalfClosedMoment D μ a q hq T e G hG)

theorem nativeStreamingEdgeCurrentCDFHalfClosedMoment_abs_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (C : ℝ) (hC : 0≤C) (hG : ∀r σ, |G r σ|≤C) (r : Paper.Overlap) :
    |nativeStreamingEdgeCurrentCDFHalfClosedMoment D μ a q T e G r|≤C := by
  rw [nativeStreamingEdgeCurrentCDFHalfClosedMoment,abs_mul,
    abs_of_nonneg (Paper.parisiCDF_nonneg μ r)]
  exact (mul_le_mul (Paper.parisiCDF_le_one μ r)
    (nativeStreamingEdgeCurrentFamilyHalfClosedMoment_abs_le D μ a q T e G C hC hG r)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul C)

theorem tendsto_nativeStreamingEdgeCurrentCDFHalfClosedIntegral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (hlo : q (e.depth+1)∈S) (hhi : q e.depth∈S)
    (GN : ℕ → Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (hGN : ∀N σ, Continuous (fun r => GN N r σ))
    (hG : ∀r σ, Tendsto (fun N => GN N (FRSB.preservingRound S N r) σ) atTop (𝓝 (G r σ)))
    (C : ℝ) (hC : 0≤C) (hbound : ∀N r σ, |GN N r σ|≤C) :
    Tendsto (fun N => ∫r, nativeStreamingEdgeCurrentCDFHalfClosedMoment D
      (FRSB.preservingMeasure μ S N) a q T e (GN N) r
        ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a) atTop
      (𝓝 (∫r, nativeStreamingEdgeCurrentCDFHalfClosedMoment D μ a q T e G r
        ∂parisiFreeMeasure μ a)) := by
  apply nativeStreaming_free_integral_tendsto μ S hzero a ha hμ _ _
    (fun N => measurable_nativeStreamingEdgeCurrentCDFHalfClosedMoment D _ a q hq T e
      (GN N) (hGN N)) C hC
    (fun N r => nativeStreamingEdgeCurrentCDFHalfClosedMoment_abs_le D _ a q T e
      (GN N) C hC (hbound N) r)
  intro r
  exact (nativeStreaming_preserving_cdf_at_round_tendsto μ S r).mul
    (nativeStreamingEdgeCurrentFamilyHalfClosedMoment_preserving_tendsto D μ a q hq T e S
      hlo hhi GN G hG r)


theorem integral_nativeStreamingEdgeSingleFamilyHalfClosedMoment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × Configuration n → ℝ) :
    (∫r, nativeStreamingEdgeSingleFamilyHalfClosedMoment D μ a q T e G r
      ∂parisiFreeMeasure μ a) =
    ∫r in Ioc (q (e.depth+1)) (q e.depth), nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgeSingleMarkProbability D μ a q T e r) (G r)
      ∂parisiFreeMeasure μ a := by
  rw [←integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall fun r => by
    simp only [nativeStreamingEdgeSingleFamilyHalfClosedMoment, Set.indicator, mem_Ioc]

theorem integral_nativeStreamingEdgeCurrentFamilyHalfClosedMoment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ) :
    (∫r, nativeStreamingEdgeCurrentFamilyHalfClosedMoment D μ a q T e G r
      ∂parisiFreeMeasure μ a) =
    ∫r in Ioc (q (e.depth+1)) (q e.depth), nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgeCurrentPairProbability D μ a q T e r) (G r)
      ∂parisiFreeMeasure μ a := by
  rw [←integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall fun r => by
    simp only [nativeStreamingEdgeCurrentFamilyHalfClosedMoment, Set.indicator, mem_Ioc]

end QuantitativeFollowup
