module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairObservedLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPairObservationIndices

@[expose] public section

/-! A fixed refined native genealogy realizes the genuine old record and
two fresh terminal marks. Its weak-profile and moving-time limits follow
from the actual whole genealogical law, with diagonal atoms retained. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 def nativeStreamingEdgePairProbabilityFixed (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (p k : ℕ) (r l : Paper.Overlap) :
    ProbabilityMeasure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
        (Configuration n × Configuration n)) :=
  (nativeStreamingCrossVertexProbability D μ a
    (nativeStreamingPairObservationSchedule q e.depth f.depth r l)
    (observationRefineTree nativeStreamingPairObservationSubdivision T)
    (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e p)
    (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision f k)).map
      (fun z=>((z.1.1,observationRefinementProject nativeStreamingPairObservationSubdivision T z.1.2),z.2))

 theorem tendsto_nativeStreamingEdgePairProbabilityFixed
    {L : Type*} {filt : Filter L} [filt.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μj : L→Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (hμ : Tendsto μj filt (𝓝 μ))
    (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T) (p k : ℕ)
    {rj lj : L→Paper.Overlap} {r l : Paper.Overlap}
    (hr : Tendsto rj filt (𝓝 r)) (hl : Tendsto lj filt (𝓝 l))
    (hrj : ∀N,q (e.depth+1)≤rj N ∧ rj N≤q e.depth)
    (hlj : ∀N,q (f.depth+1)≤lj N ∧ lj N≤q f.depth)
    (hrr : q (e.depth+1)≤r ∧ r≤q e.depth)
    (hll : q (f.depth+1)≤l ∧ l≤q f.depth) :
    Tendsto (fun N=>nativeStreamingEdgePairProbabilityFixed D (μj N) a q T e f p k (rj N) (lj N)) filt
      (𝓝 (nativeStreamingEdgePairProbabilityFixed D μ a q T e f p k r l)) := by
  haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T) :=
    anisotropicObservationRecords_borel T
  haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T) :=
    inferInstance
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_nativeStreamingCrossVertexProbability D hμ a
      (fun N=>nativeStreamingPairObservationSchedule q e.depth f.depth (rj N) (lj N))
      (nativeStreamingPairObservationSchedule q e.depth f.depth r l)
      (observationRefineTree nativeStreamingPairObservationSubdivision T)
      (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision e p)
      (nativeStreamingEdgeSelectedVertex nativeStreamingPairObservationSubdivision f k)
      (fun j _=>tendsto_nativeStreamingPairObservationSchedule q e.depth f.depth j hr hl)
      (fun N j _=>nativeStreamingPairObservationSchedule_antitone q hq e.depth f.depth
        (rj N) (lj N) (hrj N) (hlj N) (Nat.le_succ j))
      (fun j _=>nativeStreamingPairObservationSchedule_antitone q hq e.depth f.depth r l hrr hll
        (Nat.le_succ j)))
  exact (continuous_fst.fst.prodMk
    ((continuous_observationRefinementProject nativeStreamingPairObservationSubdivision T).comp
      continuous_fst.snd)).prodMk continuous_snd

end QuantitativeFollowup
