module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeMarkIntegral
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCurrentPairContinuity
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMovingTerminalMoments

@[expose] public section

/-! Current two-fresh-spin tests include the moving ancestral clock. Both
terminal draws use the actual conditional product kernel; the CDF factor
is retained before passage to the genuine free integral. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem continuousOn_nativeStreamingEdgeCurrentFamilyMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun r => G r σ)) :
    ContinuousOn (fun r => nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgeCurrentPairProbability D μ a q T e r) (G r))
        (Icc (q (e.depth+1)) (q e.depth)) := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_iff_continuousAt.mpr
  intro r
  apply tendsto_nativeStreamingMovingTerminalMarkMoment
    (tendsto_nativeStreamingEdgeCurrentPairProbability D tendsto_const_nhds a q hq T e
      (continuous_subtype_val.tendsto r) (fun z => z.2) r.2)
  exact fun σ => ((hG σ).comp continuous_subtype_val).tendsto r

def nativeStreamingEdgeCurrentFamilyMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (r : Paper.Overlap) : ℝ :=
  if q (e.depth+1)<r ∧ r<q e.depth ∧ r∉S then
    nativeStreamingTerminalMarkMoment (nativeStreamingEdgeCurrentPairProbability D μ a q T e r)
      (G r) else 0

theorem measurable_nativeStreamingEdgeCurrentFamilyMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun r => G r σ)) :
    Measurable (nativeStreamingEdgeCurrentFamilyMaskedMoment D μ a q T e S G) := by
  classical
  have hc := continuousOn_nativeStreamingEdgeCurrentFamilyMoment D μ a q hq T e G hG
  have hs : MeasurableSet {r : Paper.Overlap | q (e.depth+1)<r ∧ r<q e.depth ∧ r∉S} :=
    isOpen_Ioi.measurableSet.inter
      (isOpen_Iio.measurableSet.inter S.finite_toSet.measurableSet.compl)
  convert (hc.mono (fun r hr => ⟨hr.1.le,hr.2.1.le⟩)).measurable_piecewise
    (g:=fun _ => (0:ℝ)) continuousOn_const hs using 1
  funext r
  by_cases hr : q (e.depth+1)<r ∧ r<q e.depth ∧ r∉S <;>
    simp [nativeStreamingEdgeCurrentFamilyMaskedMoment,Set.piecewise,hr]

theorem nativeStreamingEdgeCurrentFamilyMaskedMoment_abs_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (C : ℝ) (hC : 0≤C) (hG : ∀r σ, |G r σ|≤C) (r : Paper.Overlap) :
    |nativeStreamingEdgeCurrentFamilyMaskedMoment D μ a q T e S G r|≤C := by
  classical
  unfold nativeStreamingEdgeCurrentFamilyMaskedMoment
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

theorem nativeStreamingEdgeCurrentFamilyMaskedMoment_preserving_tendsto
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (S : Finset Paper.Overlap)
    (hlo : q (e.depth+1)∈S) (hhi : q e.depth∈S)
    (GN : ℕ → Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (hG : ∀r σ, Tendsto (fun N => GN N (FRSB.preservingRound S N r) σ) atTop (𝓝 (G r σ)))
    (r : Paper.Overlap) :
    Tendsto (fun N => nativeStreamingEdgeCurrentFamilyMaskedMoment D
      (FRSB.preservingMeasure μ S N) a q T e S (GN N) (FRSB.preservingRound S N r))
        atTop (𝓝 (nativeStreamingEdgeCurrentFamilyMaskedMoment D μ a q T e S G r)) := by
  classical
  have hm (N : ℕ) :
      (q (e.depth+1)<FRSB.preservingRound S N r ∧
        FRSB.preservingRound S N r<q e.depth ∧ FRSB.preservingRound S N r∉S) ↔
      (q (e.depth+1)<r ∧ r<q e.depth ∧ r∉S) := by
    simp only [FRSB.preservingRound_gt_iff S N r _ hlo,
      FRSB.preservingRound_lt_iff S N r _ hhi,nativeStreaming_round_mem_prescribed_iff]
  by_cases hr : q (e.depth+1)<r ∧ r<q e.depth ∧ r∉S
  · have hp := tendsto_nativeStreamingEdgeCurrentPairProbability D
      (FRSB.tendsto_preservingMeasure μ S) a q hq T e (FRSB.tendsto_preservingRound S r)
      (fun N => ⟨((hm N).mpr hr).1.le,((hm N).mpr hr).2.1.le⟩)
      ⟨hr.1.le,hr.2.1.le⟩
    simpa [nativeStreamingEdgeCurrentFamilyMaskedMoment,hm,hr] using
      tendsto_nativeStreamingMovingTerminalMarkMoment hp
        (fun N => GN N (FRSB.preservingRound S N r)) (G r) (hG r)
  · simpa [nativeStreamingEdgeCurrentFamilyMaskedMoment,hm,hr] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

theorem tendsto_nativeStreamingEdgeCurrentFamilyFreeIntegral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (hlo : q (e.depth+1)∈S) (hhi : q e.depth∈S)
    (GN : ℕ → Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ)
    (hGN : ∀N σ, Continuous (fun r => GN N r σ))
    (hG : ∀r σ, Tendsto (fun N => GN N (FRSB.preservingRound S N r) σ) atTop (𝓝 (G r σ)))
    (C : ℝ) (hC : 0≤C) (hbound : ∀N r σ, |GN N r σ|≤C) :
    Tendsto (fun N => ∫r, nativeStreamingEdgeCurrentFamilyMaskedMoment D
      (FRSB.preservingMeasure μ S N) a q T e S (GN N) r
        ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a) atTop
      (𝓝 (∫r, nativeStreamingEdgeCurrentFamilyMaskedMoment D μ a q T e S G r
        ∂parisiFreeMeasure μ a)) :=
  nativeStreaming_free_integral_tendsto μ S hzero a ha hμ _ _
    (fun N => measurable_nativeStreamingEdgeCurrentFamilyMaskedMoment D _ a q hq T e S
      (GN N) (hGN N)) C hC
    (fun N r => nativeStreamingEdgeCurrentFamilyMaskedMoment_abs_le D _ a q T e S
      (GN N) C hC (hbound N) r)
    (nativeStreamingEdgeCurrentFamilyMaskedMoment_preserving_tendsto D μ a q hq T e S
      hlo hhi GN G hG)

end QuantitativeFollowup
