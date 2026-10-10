module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFutureEdgePatternsLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEdgePatternsMoments

@[expose] public section

/-! Actual enlarged-tree future moments with the old terminal observable
held at the original prefix before both free draws. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

theorem continuous_nativeStreamingGeneratedSharedFutureEdgeProbability
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth) :
    Continuous (nativeStreamingGeneratedSharedFutureEdgeProbability D μ a W e j hj) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  let U := nativeStreamingGeneratedSharedFutureEdgeObserved W e j hj
  let p := nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j
  haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) W.tree) :=
    anisotropicObservationRecords_borel W.tree
  haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) W.tree) := inferInstance
  have hP := tendsto_nativeStreamingActualContinuationProbability D
    (μj:=fun _ : CavityGeneratedHistory Paper.Overlap (m+2) => μ) (μ:=μ)
    tendsto_const_nhds a (nativeStreamingGeneratedComponentClock U)
    (nativeStreamingGeneratedComponentClock U h)
    (fun d => (finiteCascadeFuturePairTree p d).tree)
    (fun d => (finiteCascadeFuturePairTree p d).spins)
    (fun d => nativeStreamingObservationPairSpins_continuous (finiteCascadeFuturePairTree p d))
    U.tree (nativeStreamingGeneratedSharedFutureEdgeAnchor W e j hj)
    (fun k _ => (nativeStreamingGeneratedComponentClock_continuous U k).tendsto h)
    (fun H k _ => nativeStreamingGeneratedComponentClock_antitone U H (Nat.le_succ k))
    (fun k _ => nativeStreamingGeneratedComponentClock_antitone U h (Nat.le_succ k))
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hP
    ((continuous_fst.fst.prodMk
      ((continuous_observationRefinementProject nativeStreamingPairObservationSubdivision W.tree).comp
        continuous_fst.snd)).prodMk continuous_snd)

def nativeStreamingGeneratedSharedFutureEdgeMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) : ℝ :=
  nativeStreamingTerminalMarkMoment (nativeStreamingGeneratedSharedFutureEdgeProbability D μ a W e j hj H)
    (nativeStreamingDefectSpinTest W.tree (F (nativeStreamingGeneratedCrossEdgePrefix H))
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureEdgeObserved W e j hj) H
        (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j)))

theorem nativeStreamingGeneratedSharedFutureEdgeMoment_append
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧ r≤nativeStreamingGeneratedComponentClock W h e.depth)
    (hl : nativeStreamingGeneratedComponentClock W h (j+1)≤l ∧ l≤nativeStreamingGeneratedComponentClock W h j)
    (hrl : r<l) :
    nativeStreamingGeneratedSharedFutureEdgeMoment D μ a W e j hj F
      (nativeStreamingGeneratedCrossEdgeAppend h r l)=
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (F h) (.future (.edge e r) j l) := by
  unfold nativeStreamingGeneratedSharedFutureEdgeMoment
  rw [nativeStreamingGeneratedSharedFutureEdgeProbability_append D μ a W e j hj h r l hh hr hl hrl,
    nativeStreamingGeneratedCrossEdgePrefix_append]
  rw [←nativeStreamingGeneratedSharedFutureEdgeComponent_clock W e j hj,
    nativeStreamingGeneratedSharedFutureEdge_split_clock W e j hj h r l hh hr hl hrl]
  rfl

theorem nativeStreamingGeneratedSharedFutureEdgeMoment_abs_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀h σ,|F h σ|≤C)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    |nativeStreamingGeneratedSharedFutureEdgeMoment D μ a W e j hj F H|≤2*C := by
  let P := nativeStreamingGeneratedSharedFutureEdgeProbability D μ a W e j hj H
  simpa only [nativeStreamingGeneratedSharedFutureEdgeMoment,nativeStreamingTerminalMarkMoment,
    Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=(P : Measure ((AnisotropicObservationState (n+1) ×
        Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) W.tree) ×
          (Configuration (n+1) × Configuration (n+1)))))
      (f:=fun z => nativeStreamingDefectSpinTest W.tree (F (nativeStreamingGeneratedCrossEdgePrefix H))
        (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureEdgeObserved W e j hj) H
          (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j))
            (finiteCascadeRecordTerminalSpins W.tree z.1.2,z.2))
      (.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using nativeStreamingDefectSpinTest_abs_le
          W.tree (F (nativeStreamingGeneratedCrossEdgePrefix H)) C hC (hF _) _
            (finiteCascadeRecordTerminalSpins W.tree z.1.2,z.2))

theorem continuous_nativeStreamingGeneratedSharedFutureEdgeMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (j : ℕ) (hj : j≤e.depth)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (hF : ∀σ,Continuous (fun h => F h σ)) :
    Continuous (nativeStreamingGeneratedSharedFutureEdgeMoment D μ a W e j hj F) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  apply tendsto_nativeStreamingMovingTerminalMarkMoment
    ((continuous_nativeStreamingGeneratedSharedFutureEdgeProbability D μ a W e j hj).tendsto h)
  intro σ
  exact (((hF σ.1).comp continuous_nativeStreamingGeneratedCrossEdgePrefix).mul
    (continuous_cavitySpinOverlapDefect_clock _
      (nativeStreamingGeneratedComponentClock_continuous
        (nativeStreamingGeneratedSharedFutureEdgeObserved W e j hj)
        (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j)) _ _)).tendsto h

end QuantitativeFollowup
