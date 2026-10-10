module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexPatternsMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFuturePairLaw

@[expose] public section

/-! A continuation at a coordinate already present in the generated
history uses that coordinate without another atom draw. Its old clocks,
all old records, and the actual normalized continuation are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def nativeStreamingGeneratedRetainedVertexComponent
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (i : Fin m) (hi : cavityGeneratedFiniteClockLabels W.label v.depth=.mark i)
    (k : NativeStreamingGeneratedVertexKind) : CavityGeneratedConstructedComponent m where
  depth := W.depth
  tree := finiteCascadeContinuationGraft k.continuation v
  label := W.label
  terminal_label := W.terminal_label
  initial_label := W.initial_label
  construction := .graft k.continuation v i hi W.construction
    (k.continuation_constructed (cavityGeneratedFiniteClockLabels W.label) v.depth i hi)

theorem nativeStreamingGeneratedRetainedVertexComponent_clock
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (i : Fin m) (hi : cavityGeneratedFiniteClockLabels W.label v.depth=.mark i)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedRetainedVertexComponent W v i hi k) h=
      nativeStreamingGeneratedComponentClock W h := rfl

theorem nativeStreamingGeneratedRetainedVertexComponent_orderSet
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (i : Fin m) (hi : cavityGeneratedFiniteClockLabels W.label v.depth=.mark i)
    (k : NativeStreamingGeneratedVertexKind) :
    nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedRetainedVertexComponent W v i hi k)=
      nativeStreamingGeneratedComponentOrderSet W := rfl

theorem nativeStreamingGeneratedRetainedVertexComponent_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (i : Fin m) (hi : cavityGeneratedFiniteClockLabels W.label v.depth=.mark i)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedRetainedVertexComponent W v i hi k) h)
      (nativeStreamingGeneratedRetainedVertexComponent W v i hi k).tree).map
      (fun z=>((z.1,(finiteCascadeContinuationExtract k.continuation k.recordMark v z.2).1),
        (finiteCascadeContinuationExtract k.continuation k.recordMark v z.2).2))=
    nativeStreamingActualContinuationLaw D μ a (nativeStreamingGeneratedComponentClock W h)
      k.continuation k.recordMark W.tree v :=
  nativeStreamingActualContinuationLaw_eq_graft D μ a _ k.continuation k.recordMark
    (fun j=>k.recordMark_measurable j) W.tree v

theorem cavityGeneratedFuturePairTree_constructed
    (labels : ℕ→CavityGeneratedClockLabel m) (p d : ℕ) (hp : p≤d)
    (i : Fin m) (hi : labels p=.mark i) :
    CavityGeneratedGenealogyConstruction labels (finiteCascadeFuturePairTree p d).tree := by
  have hl (j : ℕ) : CavityGeneratedGenealogyConstruction labels (observationLinearTree j) := by
    rw [nativeStreamingLinearTree_eq_finite_linear]
    exact .linear j
  induction d with
  | zero =>
      have hp0 : p=0 := by omega
      subst p
      exact .fork i hi (hl 0) (hl 0)
  | succ d ih =>
      by_cases he : p=d+1
      · subst p
        simp only [finiteCascadeFuturePairTree,ite_true,ObservationPairTree.tree]
        exact .fork i hi (hl (d+1)) (hl (d+1))
      · simp only [finiteCascadeFuturePairTree,if_neg he,ObservationPairTree.tree]
        exact .advance (ih (by omega))

def nativeStreamingGeneratedRetainedFutureComponent
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (b : Fin m) (hb : cavityGeneratedFiniteClockLabels W.label v.depth=.mark b)
    (p : ℕ) (hp : p≤v.depth)
    (c : Fin m) (hc : cavityGeneratedFiniteClockLabels W.label p=.mark c) :
    CavityGeneratedConstructedComponent m where
  depth := W.depth
  tree := finiteCascadeFutureVertexGraft v p
  label := W.label
  terminal_label := W.terminal_label
  initial_label := W.initial_label
  construction := .graft (fun d=>(finiteCascadeFuturePairTree p d).tree) v b hb W.construction
    (cavityGeneratedFuturePairTree_constructed (cavityGeneratedFiniteClockLabels W.label) p v.depth hp c hc)

theorem nativeStreamingGeneratedRetainedFutureComponent_clock
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (b : Fin m) (hb : cavityGeneratedFiniteClockLabels W.label v.depth=.mark b)
    (p : ℕ) (hp : p≤v.depth)
    (c : Fin m) (hc : cavityGeneratedFiniteClockLabels W.label p=.mark c)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedRetainedFutureComponent W v b hb p hp c hc) h=
      nativeStreamingGeneratedComponentClock W h := rfl

theorem nativeStreamingGeneratedRetainedFutureComponent_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (b : Fin m) (hb : cavityGeneratedFiniteClockLabels W.label v.depth=.mark b)
    (p : ℕ) (hp : p≤v.depth)
    (c : Fin m) (hc : cavityGeneratedFiniteClockLabels W.label p=.mark c)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedRetainedFutureComponent W v b hb p hp c hc) h)
      (nativeStreamingGeneratedRetainedFutureComponent W v b hb p hp c hc).tree).map
      (fun z=>((z.1,(finiteCascadeFutureGraftExtract v p z.2).1),
        (finiteCascadeFutureGraftExtract v p z.2).2))=
    nativeStreamingFuturePairLaw D μ a (nativeStreamingGeneratedComponentClock W h) W.tree v
      (nativeStreamingGeneratedComponentClock W h p) :=
  nativeStreamingFuturePairLaw_eq_graft D μ a _
    (nativeStreamingGeneratedComponentClock_antitone W h)
    (nativeStreamingGeneratedComponentClock_terminal W h) W.tree v p hp

end QuantitativeFollowup
