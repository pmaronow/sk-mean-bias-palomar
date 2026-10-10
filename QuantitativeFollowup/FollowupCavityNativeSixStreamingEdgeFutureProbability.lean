module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeFutureSelectedLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPairObservationIndices

@[expose] public section

/-! A fixed two-slot genealogy realizes an edge ancestor and a shared
future split. Its whole old-record and terminal-pair law has genuine
weak-profile and moving-time convergence. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def nativeStreamingEdgeFutureProbabilityFixed (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (j p k : ℕ) (r l : Paper.Overlap) :
    ProbabilityMeasure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
        (Configuration n × Configuration n)) :=
  (nativeStreamingActualContinuationProbability D μ a
    (nativeStreamingPairObservationSchedule q e.depth j r l)
    (fun v=>(finiteCascadeFuturePairTree
      (observationRefinementDepth nativeStreamingPairObservationSubdivision j+k+1) v).tree)
    (fun v=>(finiteCascadeFuturePairTree
      (observationRefinementDepth nativeStreamingPairObservationSubdivision j+k+1) v).spins)
    (observationRefineTree nativeStreamingPairObservationSubdivision T)
    (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e p)).map
      (fun z=>((z.1.1,observationRefinementProject nativeStreamingPairObservationSubdivision T z.1.2),z.2))

theorem nativeStreamingEdgeFutureProbabilityFixed_eq_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (hq : Antitone q) (hzero : q 0=1) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (j p k : ℕ) (hp : p<2)
    (hfuture : observationRefinementDepth nativeStreamingPairObservationSubdivision j+k+1≤
      observationRefinementDepth nativeStreamingPairObservationSubdivision e.depth+p+1)
    (r l : Paper.Overlap) (hr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (hl : q (j+1)≤l ∧ l≤q j) :
    (nativeStreamingEdgeFutureProbabilityFixed D μ a q T e j p k r l : Measure _)=
      ((anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q T e
        (nativeStreamingPairObservationSchedule q e.depth j r l
          (observationRefinementDepth nativeStreamingPairObservationSubdivision e.depth+p+1))) ⊗ₘ
            nativeStreamingEdgeObservedFutureKernel D μ T
              (nativeStreamingPairObservationSchedule q e.depth j r l
                (observationRefinementDepth nativeStreamingPairObservationSubdivision e.depth+p+1))
              (nativeStreamingPairObservationSchedule q e.depth j r l
                (observationRefinementDepth nativeStreamingPairObservationSubdivision j+k+1))).map
                  (fun z=>((z.1.1,z.1.2.2),z.2)) := by
  let Q := nativeStreamingPairObservationSchedule q e.depth j r l
  let V := nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e p
  have hQ : Antitone Q := nativeStreamingPairObservationSchedule_antitone q hq e.depth j r l hr hl
  have hQ0 : Q 0=1 := by
    simpa only [Q,nativeStreamingPairObservationSchedule,Nat.zero_mod,Nat.zero_div,ite_true] using hzero
  have hV : observationRefinementDepth nativeStreamingPairObservationSubdivision j+k+1≤V.depth := by
    rw [nativeStreamingEdgeSelectedVertex_depth _ e p hp]
    exact hfuture
  have hg := nativeStreamingFuturePairLaw_eq_graft D μ a Q hQ hQ0
    (observationRefineTree nativeStreamingPairObservationSubdivision T) V
    (observationRefinementDepth nativeStreamingPairObservationSubdivision j+k+1) hV
  change Measure.map _ ((anisotropicRecordedProfileTreeLaw D μ a Q _).map _)=_
  rw [hg]
  exact nativeStreamingEdgeSelectedFutureLaw_projection D μ a q Q
    nativeStreamingPairObservationSubdivision hQ
    (nativeStreamingPairObservationSchedule_refinement q e.depth j r l) e p hp _

theorem tendsto_nativeStreamingEdgeFutureProbabilityFixed
    {L : Type*} {filt : Filter L} [filt.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μj : L→Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (hμ : Tendsto μj filt (𝓝 μ))
    (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (j p k : ℕ)
    {rj lj : L→Paper.Overlap} {r l : Paper.Overlap}
    (hr : Tendsto rj filt (𝓝 r)) (hl : Tendsto lj filt (𝓝 l))
    (hrj : ∀N,q (e.depth+1)≤rj N ∧ rj N≤q e.depth)
    (hlj : ∀N,q (j+1)≤lj N ∧ lj N≤q j)
    (hrr : q (e.depth+1)≤r ∧ r≤q e.depth) (hll : q (j+1)≤l ∧ l≤q j) :
    Tendsto (fun N=>nativeStreamingEdgeFutureProbabilityFixed D (μj N) a q T e j p k
      (rj N) (lj N)) filt
      (𝓝 (nativeStreamingEdgeFutureProbabilityFixed D μ a q T e j p k r l)) := by
  haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T) :=
    anisotropicObservationRecords_borel T
  haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T) :=
    inferInstance
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_nativeStreamingActualContinuationProbability D hμ a
      (fun N=>nativeStreamingPairObservationSchedule q e.depth j (rj N) (lj N))
      (nativeStreamingPairObservationSchedule q e.depth j r l)
      (fun v=>(finiteCascadeFuturePairTree
        (observationRefinementDepth nativeStreamingPairObservationSubdivision j+k+1) v).tree)
      (fun v=>(finiteCascadeFuturePairTree
        (observationRefinementDepth nativeStreamingPairObservationSubdivision j+k+1) v).spins)
      (fun v=>nativeStreamingObservationPairSpins_continuous (finiteCascadeFuturePairTree
        (observationRefinementDepth nativeStreamingPairObservationSubdivision j+k+1) v))
      (observationRefineTree nativeStreamingPairObservationSubdivision T)
      (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e p)
      (fun v _=>tendsto_nativeStreamingPairObservationSchedule q e.depth j v hr hl)
      (fun N v _=>nativeStreamingPairObservationSchedule_antitone q hq e.depth j
        (rj N) (lj N) (hrj N) (hlj N) (Nat.le_succ v))
      (fun v _=>nativeStreamingPairObservationSchedule_antitone q hq e.depth j r l hrr hll
        (Nat.le_succ v)))
  exact (continuous_fst.fst.prodMk
    ((continuous_observationRefinementProject nativeStreamingPairObservationSubdivision T).comp
      continuous_fst.snd)).prodMk continuous_snd

theorem nativeStreamingPairObservationIndex_future_le (de j : ℕ) (r l : Paper.Overlap)
    (hj : j≤de) (hrl : r≤l) :
    observationRefinementDepth nativeStreamingPairObservationSubdivision j+
      nativeStreamingPairObservationIndex j de l r+1≤
        observationRefinementDepth nativeStreamingPairObservationSubdivision de+
          nativeStreamingPairObservationIndex de j r l+1 := by
  rw [nativeStreamingPairObservationSubdivision_depth,nativeStreamingPairObservationSubdivision_depth]
  have hn : ¬l<r := not_lt_of_ge hrl
  by_cases he : de=j
  · subst j
    simp only [nativeStreamingPairObservationIndex,ite_true,hn,ite_false]
    split_ifs <;> omega
  · simp only [nativeStreamingPairObservationIndex,if_neg he,if_neg (Ne.symm he)]
    omega

end QuantitativeFollowup
