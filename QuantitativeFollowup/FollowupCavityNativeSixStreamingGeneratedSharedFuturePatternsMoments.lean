module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFuturePatternsLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEdgePatternsMoments

@[expose] public section

/-! The shared-future test keeps the original history prefix and the
complete old record. The genuine continuation probability is the
pushforward of the enlarged genealogy, with a single inserted split. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def nativeStreamingGeneratedSharedFutureProbability
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    ProbabilityMeasure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) W.tree) ×
        (Configuration n × Configuration n)) :=
  (nativeStreamingActualContinuationProbability D μ a
    (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeObservedComponent W e) H)
    (fun d => (finiteCascadeFuturePairTree (e.depth+1) d).tree)
    (fun d => (finiteCascadeFuturePairTree (e.depth+1) d).spins)
    (nativeStreamingGeneratedEdgeObservedComponent W e).tree
    (nativeStreamingGeneratedSharedFutureAnchor W v e)).map
      (fun z => ((z.1.1,observationRefinementProject
        (nativeStreamingEdgeSubdivision e.depth) W.tree z.1.2),z.2))

theorem nativeStreamingGeneratedSharedFutureProbability_snoc
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock W h e.depth) :
    nativeStreamingGeneratedSharedFutureProbability D μ a W v e (Fin.snoc h r) =
      nativeStreamingOriginFutureProbability D μ a
        (nativeStreamingGeneratedComponentClock W h) W.tree (.vertex v) e.depth r := by
  unfold nativeStreamingGeneratedSharedFutureProbability
  rw [nativeStreamingGeneratedEdgeObservedComponent_clock_snoc W e h r hh hr]
  rfl

theorem continuous_nativeStreamingGeneratedSharedFutureProbability
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree) :
    Continuous (nativeStreamingGeneratedSharedFutureProbability D μ a W v e) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  let U := nativeStreamingGeneratedEdgeObservedComponent W e
  haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) W.tree) :=
    anisotropicObservationRecords_borel W.tree
  haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) W.tree) :=
    inferInstance
  have hP := tendsto_nativeStreamingActualContinuationProbability D
    (μj:=fun _ : CavityGeneratedHistory Paper.Overlap (m+1) => μ) (μ:=μ)
    tendsto_const_nhds a (nativeStreamingGeneratedComponentClock U)
    (nativeStreamingGeneratedComponentClock U h)
    (fun d => (finiteCascadeFuturePairTree (e.depth+1) d).tree)
    (fun d => (finiteCascadeFuturePairTree (e.depth+1) d).spins)
    (fun d => nativeStreamingObservationPairSpins_continuous
      (finiteCascadeFuturePairTree (e.depth+1) d)) U.tree
    (nativeStreamingGeneratedSharedFutureAnchor W v e)
    (fun p _ => (nativeStreamingGeneratedComponentClock_continuous U p).tendsto h)
    (fun H p _ => nativeStreamingGeneratedComponentClock_antitone U H (Nat.le_succ p))
    (fun p _ => nativeStreamingGeneratedComponentClock_antitone U h (Nat.le_succ p))
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hP
    ((continuous_fst.fst.prodMk
      ((continuous_observationRefinementProject (nativeStreamingEdgeSubdivision e.depth) W.tree).comp
        continuous_fst.snd)).prodMk continuous_snd)

def nativeStreamingGeneratedSharedFutureMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) : ℝ :=
  nativeStreamingTerminalMarkMoment (nativeStreamingGeneratedSharedFutureProbability D μ a W v e H)
    (nativeStreamingDefectSpinTest W.tree (F (cavityGeneratedHistoryPrefix H))
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeObservedComponent W e) H
        (e.depth+1)))

theorem nativeStreamingGeneratedSharedFutureMoment_snoc
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock W h e.depth) :
    nativeStreamingGeneratedSharedFutureMoment D μ a W v e F (Fin.snoc h r) =
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (F h) (.future (.vertex v) e.depth r) := by
  unfold nativeStreamingGeneratedSharedFutureMoment
  rw [nativeStreamingGeneratedSharedFutureProbability_snoc D μ a W v e h r hh hr,
    cavityGeneratedHistoryPrefix_snoc,
    nativeStreamingGeneratedEdgeObservedComponent_clock_snoc W e h r hh hr,
    nativeStreamingEdgeSchedule_inserted]
  rfl

theorem nativeStreamingGeneratedSharedFutureMoment_abs_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀h σ, |F h σ| ≤ C)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    |nativeStreamingGeneratedSharedFutureMoment D μ a W v e F H| ≤ 2*C := by
  let P := nativeStreamingGeneratedSharedFutureProbability D μ a W v e H
  simpa only [nativeStreamingGeneratedSharedFutureMoment,nativeStreamingTerminalMarkMoment,
    Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=(P : Measure ((AnisotropicObservationState (n+1) ×
        Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) W.tree) ×
          (Configuration (n+1) × Configuration (n+1)))))
      (f:=fun z => nativeStreamingDefectSpinTest W.tree (F (cavityGeneratedHistoryPrefix H))
        (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeObservedComponent W e) H
          (e.depth+1)) (finiteCascadeRecordTerminalSpins W.tree z.1.2,z.2))
      (.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using nativeStreamingDefectSpinTest_abs_le
          W.tree (F (cavityGeneratedHistoryPrefix H)) C hC (hF _) _
            (finiteCascadeRecordTerminalSpins W.tree z.1.2,z.2))

theorem continuous_nativeStreamingGeneratedSharedFutureMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (hF : ∀σ, Continuous (fun h => F h σ)) :
    Continuous (nativeStreamingGeneratedSharedFutureMoment D μ a W v e F) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  apply tendsto_nativeStreamingMovingTerminalMarkMoment
    ((continuous_nativeStreamingGeneratedSharedFutureProbability D μ a W v e).tendsto h)
  intro σ
  exact (((hF σ.1).comp continuous_cavityGeneratedHistoryPrefix).mul
    (continuous_cavitySpinOverlapDefect_clock _
      (nativeStreamingGeneratedComponentClock_continuous
        (nativeStreamingGeneratedEdgeObservedComponent W e) (e.depth+1)) _ _)).tendsto h

end QuantitativeFollowup
