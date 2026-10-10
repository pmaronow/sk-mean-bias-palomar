module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexPatternsTerminal

@[expose] public section

/-! The genuine enlarged genealogy retains the whole original record and
has exactly the normalized one- or two-continuation law. Its terminal test
is the actual original/fresh or current-pair overlap defect. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m J : ℕ}

def nativeStreamingGeneratedVertexMoment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (k : NativeStreamingGeneratedVertexKind)
    (G : TerminalSpins (Configuration n) T × k.Mark (Configuration n) → ℝ) : ℝ :=
  ∫ z, G (nativeStreamingGeneratedVertexTerminalProjection k v
      (finiteCascadeRecordTerminalSpins _ z.2))
    ∂anisotropicRecordedProfileTreeLaw D μ a q (finiteCascadeContinuationGraft k.continuation v)

theorem nativeStreamingGeneratedVertexMoment_eq_terminalMarkMoment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (k : NativeStreamingGeneratedVertexKind)
    (G : TerminalSpins (Configuration n) T × k.Mark (Configuration n) → ℝ) :
    nativeStreamingGeneratedVertexMoment D μ a q T v k G =
      nativeStreamingTerminalMarkMoment
        (nativeStreamingActualContinuationProbability D μ a q k.continuation k.recordMark T v) G := by
  let ψ := fun z : AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n)
        (finiteCascadeContinuationGraft k.continuation v) =>
      ((z.1,(finiteCascadeContinuationExtract k.continuation k.recordMark v z.2).1),
        (finiteCascadeContinuationExtract k.continuation k.recordMark v z.2).2)
  have he := measurable_finiteCascadeContinuationExtract (E:=AnisotropicObservationState n)
    (S:=Configuration n) k.continuation k.recordMark
    (fun j => k.recordMark_measurable (E:=AnisotropicObservationState n) (S:=Configuration n) j) v
  have hm : Measurable ψ :=
    (measurable_fst.prodMk (he.fst.comp measurable_snd)).prodMk (he.snd.comp measurable_snd)
  have hc : Continuous (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) × k.Mark (Configuration n)) =>
      G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (continuous_of_discreteTopology (f:=G)).comp
      (((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_fst.snd).prodMk continuous_snd)
  unfold nativeStreamingTerminalMarkMoment nativeStreamingActualContinuationProbability
  rw [ProbabilityMeasure.toMeasure_map,integral_map hm.aemeasurable hc.aestronglyMeasurable]
  unfold nativeStreamingGeneratedVertexMoment
  apply integral_congr_ae
  exact .of_forall fun z => congrArg G (nativeStreamingGeneratedVertexTerminalProjection_record k v z.2)

theorem nativeStreamingGeneratedVertex_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (k : NativeStreamingGeneratedVertexKind) :
    (anisotropicRecordedProfileTreeLaw D μ a q (finiteCascadeContinuationGraft k.continuation v)).map
      (fun z => ((z.1,(finiteCascadeContinuationExtract k.continuation k.recordMark v z.2).1),
        (finiteCascadeContinuationExtract k.continuation k.recordMark v z.2).2)) =
      nativeStreamingActualContinuationLaw D μ a q k.continuation k.recordMark T v :=
  nativeStreamingActualContinuationLaw_eq_graft D μ a q k.continuation k.recordMark
    (fun j => k.recordMark_measurable j) T v

theorem nativeStreamingGeneratedVertexMoment_eq_conditional_integral
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (k : NativeStreamingGeneratedVertexKind)
    (G : TerminalSpins (Configuration n) T × k.Mark (Configuration n) → ℝ) :
    nativeStreamingGeneratedVertexMoment D μ a q T v k G =
      ∫ z, ∫ s, G (finiteCascadeRecordTerminalSpins T z.2,s)
        ∂((anisotropicRecordedProfileTreeKernel D μ q (k.continuation v.depth)).map
          (k.recordMark v.depth)) (nativeStreamingVertexState v z.1 z.2)
        ∂anisotropicRecordedProfileTreeLaw D μ a q T := by
  rw [nativeStreamingGeneratedVertexMoment_eq_terminalMarkMoment]
  exact nativeStreamingActualContinuationTerminalMoment_eq_integral D μ a q k.continuation
    k.recordMark (fun j => k.recordMark_measurable j) T v G

theorem nativeStreamingGeneratedVertexMoment_originalFresh
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) :
    nativeStreamingGeneratedVertexMoment D μ a q T v .single
      (nativeStreamingOriginalFreshSpinTest T F i
        (q (finiteCascadeCommonPathDepth T (observationLeafVertex T i) v))) =
      nativeStreamingPatternMoment D μ a q T F (.originalFresh i (.vertex v)) := by
  exact nativeStreamingGeneratedVertexMoment_eq_terminalMarkMoment D μ a q T v .single _

theorem nativeStreamingGeneratedVertexMoment_current
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingGeneratedVertexMoment D μ a q T v .current
      (nativeStreamingDefectSpinTest T F (q v.depth)) =
      nativeStreamingPatternMoment D μ a q T F (.current (.vertex v)) := by
  exact nativeStreamingGeneratedVertexMoment_eq_terminalMarkMoment D μ a q T v .current _

theorem nativeStreamingGeneratedVertexMoment_abs_le
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (k : NativeStreamingGeneratedVertexKind)
    (G : TerminalSpins (Configuration n) T × k.Mark (Configuration n) → ℝ)
    (C : ℝ) (hG : ∀σ, |G σ| ≤ C) :
    |nativeStreamingGeneratedVertexMoment D μ a q T v k G| ≤ C := by
  rw [nativeStreamingGeneratedVertexMoment_eq_terminalMarkMoment]
  simpa only [nativeStreamingTerminalMarkMoment,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=(nativeStreamingActualContinuationProbability D μ a q k.continuation k.recordMark T v :
        Measure ((AnisotropicObservationState n × Records (AnisotropicObservationState n)
          (Configuration n) T) × k.Mark (Configuration n))))
      (f:=fun z => G (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
      (.of_forall fun z => by simpa only [Real.norm_eq_abs] using
        (hG (finiteCascadeRecordTerminalSpins T z.1.2,z.2)))

theorem continuous_nativeStreamingGeneratedVertexMoment
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (k : NativeStreamingGeneratedVertexKind)
    (G : CavityGeneratedHistory Paper.Overlap m →
      TerminalSpins (Configuration n) W.tree × k.Mark (Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun h => G h σ)) :
    Continuous (fun h => nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock W h) W.tree v k (G h)) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  change Tendsto (fun H => nativeStreamingGeneratedVertexMoment D μ a
    (nativeStreamingGeneratedComponentClock W H) W.tree v k (G H)) (𝓝 h)
    (𝓝 (nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock W h) W.tree v k (G h)))
  have hP := tendsto_nativeStreamingActualContinuationProbability D
    (μj:=fun _ : CavityGeneratedHistory Paper.Overlap m => μ) (μ:=μ) tendsto_const_nhds a
    (nativeStreamingGeneratedComponentClock W) (nativeStreamingGeneratedComponentClock W h)
    k.continuation k.recordMark (fun j => k.recordMark_continuous j) W.tree v
    (fun p _ => (nativeStreamingGeneratedComponentClock_continuous W p).tendsto h)
    (fun H p _ => nativeStreamingGeneratedComponentClock_antitone W H (Nat.le_succ p))
    (fun p _ => nativeStreamingGeneratedComponentClock_antitone W h (Nat.le_succ p))
  simpa only [nativeStreamingGeneratedVertexMoment_eq_terminalMarkMoment] using
    tendsto_nativeStreamingMovingTerminalMarkMoment hP G (G h) (fun σ => (hG σ).tendsto h)

end QuantitativeFollowup
