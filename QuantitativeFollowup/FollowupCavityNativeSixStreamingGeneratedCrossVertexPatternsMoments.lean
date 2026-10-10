module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossVertexPatternsTerminal
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossVertexPatternsHistory

@[expose] public section

/-! Actual double-graft terminal moments are genuine cross-source
moments. Their continuity and bounds follow from the normalized enlarged
law and finite terminal-spin space, not from a supplied moment equality. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m J : ℕ}

def nativeStreamingGeneratedCrossVertexMoment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × (Configuration n×Configuration n) → ℝ) : ℝ :=
  ∫z, G (nativeStreamingGeneratedCrossVertexTerminalProjection v w
    (finiteCascadeRecordTerminalSpins _ z.2))
    ∂anisotropicRecordedProfileTreeLaw D μ a q (finiteCascadeCrossContinuationGraft observationLinearTree v w)

theorem nativeStreamingGeneratedCrossVertexMoment_eq_terminalMarkMoment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × (Configuration n×Configuration n) → ℝ) :
    nativeStreamingGeneratedCrossVertexMoment D μ a q T v w G=
      nativeStreamingTerminalMarkMoment (nativeStreamingCrossVertexProbability D μ a q T v w) G := by
  let ψ := fun z : AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n)
        (finiteCascadeCrossContinuationGraft observationLinearTree v w) =>
      ((z.1,(finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z.2).1),
        (finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z.2).2)
  have he := measurable_finiteCascadeCrossContinuationExtract (E:=AnisotropicObservationState n)
    (S:=Configuration n) observationLinearTree observationLinearSpin
    (fun j => measurable_observationLinearSpin j) v w
  have hm : Measurable ψ :=
    (measurable_fst.prodMk (he.fst.comp measurable_snd)).prodMk (he.snd.comp measurable_snd)
  have hc : Continuous (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) × (Configuration n×Configuration n)) =>
      G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (continuous_of_discreteTopology (f:=G)).comp
      (((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_fst.snd).prodMk continuous_snd)
  unfold nativeStreamingTerminalMarkMoment nativeStreamingCrossVertexProbability
  rw [ProbabilityMeasure.toMeasure_map,integral_map hm.aemeasurable hc.aestronglyMeasurable]
  unfold nativeStreamingGeneratedCrossVertexMoment
  apply integral_congr_ae
  exact .of_forall fun z => congrArg G (nativeStreamingGeneratedCrossVertexTerminalProjection_record v w z.2)

theorem nativeStreamingGeneratedCrossVertexMoment_cross
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex T) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingGeneratedCrossVertexMoment D μ a q T v w
      (nativeStreamingDefectSpinTest T F (q (finiteCascadeCommonPathDepth T v w)))=
      nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) (.vertex w)) := by
  exact nativeStreamingGeneratedCrossVertexMoment_eq_terminalMarkMoment D μ a q T v w _

theorem nativeStreamingGeneratedCrossVertexMoment_abs_le
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × (Configuration n×Configuration n) → ℝ)
    (C : ℝ) (hG : ∀σ, |G σ|≤C) :
    |nativeStreamingGeneratedCrossVertexMoment D μ a q T v w G|≤C := by
  rw [nativeStreamingGeneratedCrossVertexMoment_eq_terminalMarkMoment]
  simpa only [nativeStreamingTerminalMarkMoment,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=(nativeStreamingCrossVertexProbability D μ a q T v w :
        Measure ((AnisotropicObservationState n × Records (AnisotropicObservationState n)
          (Configuration n) T) × (Configuration n×Configuration n))))
      (f:=fun z => G (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
      (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hG (finiteCascadeRecordTerminalSpins T z.1.2,z.2))

theorem continuous_nativeStreamingGeneratedCrossVertexMoment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex T)
    (G : CavityGeneratedHistory Paper.Overlap m →
      TerminalSpins (Configuration n) T × (Configuration n×Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun h => G h σ)) :
    Continuous (fun h => nativeStreamingGeneratedCrossVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock W h) T v w (G h)) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  change Tendsto (fun H => nativeStreamingGeneratedCrossVertexMoment D μ a
    (nativeStreamingGeneratedComponentClock W H) T v w (G H)) (𝓝 h)
    (𝓝 (nativeStreamingGeneratedCrossVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock W h) T v w (G h)))
  have hP := tendsto_nativeStreamingCrossVertexProbability D
    (μj:=fun _ : CavityGeneratedHistory Paper.Overlap m => μ) (μ:=μ) tendsto_const_nhds a
    (nativeStreamingGeneratedComponentClock W) (nativeStreamingGeneratedComponentClock W h) T v w
    (fun p _ => (nativeStreamingGeneratedComponentClock_continuous W p).tendsto h)
    (fun H p _ => nativeStreamingGeneratedComponentClock_antitone W H (Nat.le_succ p))
    (fun p _ => nativeStreamingGeneratedComponentClock_antitone W h (Nat.le_succ p))
  simpa only [nativeStreamingGeneratedCrossVertexMoment_eq_terminalMarkMoment] using
    tendsto_nativeStreamingMovingTerminalMarkMoment hP G (G h) (fun σ => (hG σ).tendsto h)

def nativeStreamingGeneratedCrossVertexPatternMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (hw0 : 0<w.depth) (hwJ : w.depth<W.depth)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) : ℝ :=
  let q := nativeStreamingGeneratedComponentClock
    (nativeStreamingGeneratedCrossVertexComponent W v w hv0 hvJ hw0 hwJ) H
  nativeStreamingGeneratedCrossVertexMoment D μ a q W.tree v w
    (nativeStreamingDefectSpinTest W.tree (F (nativeStreamingGeneratedCrossVertexPrefix H))
      (q (finiteCascadeCommonPathDepth W.tree v w)))

theorem nativeStreamingGeneratedCrossVertexPatternMoment_append
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (hw0 : 0<w.depth) (hwJ : w.depth<W.depth)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedCrossVertexPatternMoment D μ a W v w hv0 hvJ hw0 hwJ F
      (nativeStreamingGeneratedCrossVertexAppend W v w h)=
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h) W.tree
        (F h) (.cross (.vertex v) (.vertex w)) := by
  unfold nativeStreamingGeneratedCrossVertexPatternMoment
  dsimp only
  rw [nativeStreamingGeneratedCrossVertexComponent_clock_append,
    nativeStreamingGeneratedCrossVertexPrefix_append,nativeStreamingGeneratedCrossVertexMoment_cross]

theorem nativeStreamingGeneratedCrossVertexPatternMoment_abs_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (hw0 : 0<w.depth) (hwJ : w.depth<W.depth)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀h σ, |F h σ|≤C)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    |nativeStreamingGeneratedCrossVertexPatternMoment D μ a W v w hv0 hvJ hw0 hwJ F H|≤2*C := by
  apply nativeStreamingGeneratedCrossVertexMoment_abs_le
  intro σ
  exact nativeStreamingDefectSpinTest_abs_le W.tree _ C hC (hF _) _ σ

theorem continuous_nativeStreamingGeneratedCrossVertexPatternMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (hw0 : 0<w.depth) (hwJ : w.depth<W.depth)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (hF : ∀σ, Continuous (fun h => F h σ)) :
    Continuous (nativeStreamingGeneratedCrossVertexPatternMoment D μ a W v w hv0 hvJ hw0 hwJ F) := by
  unfold nativeStreamingGeneratedCrossVertexPatternMoment
  dsimp only
  apply continuous_nativeStreamingGeneratedCrossVertexMoment D μ a
    (nativeStreamingGeneratedCrossVertexComponent W v w hv0 hvJ hw0 hwJ) W.tree v w
  intro σ
  exact ((hF σ.1).comp continuous_nativeStreamingGeneratedCrossVertexPrefix).mul
    (continuous_cavitySpinOverlapDefect_clock _
      (nativeStreamingGeneratedComponentClock_continuous
        (nativeStreamingGeneratedCrossVertexComponent W v w hv0 hvJ hw0 hwJ) _) _ _)

end QuantitativeFollowup
