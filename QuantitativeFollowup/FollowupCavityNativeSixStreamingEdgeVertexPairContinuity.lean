module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCrossMarkedLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeMarkLaw

@[expose] public section

/-! One retained branch vertex and one genuine ancestral edge mark carry
independent terminal continuations under their actual common old record.
The original history is retained under weak-profile/moving-mark limits. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

def nativeStreamingEdgeVertexPairProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T) (r : Paper.Overlap) :=
  (nativeStreamingCrossVertexProbability D μ a (nativeStreamingEdgeSchedule q e.depth r)
    (observationRefineTree (nativeStreamingEdgeSubdivision e.depth) T)
    (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
    (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v)).map
      (fun z => ((z.1.1,observationRefinementProject (nativeStreamingEdgeSubdivision e.depth)
        T z.1.2),z.2))

theorem tendsto_nativeStreamingEdgeVertexPairProbability
    {L : Type*} {l : Filter L} [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μj : L → Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (hμ : Tendsto μj l (𝓝 μ))
    (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (v : FiniteCascadeRecordVertex T)
    {rj : L → Paper.Overlap} {r : Paper.Overlap} (hr : Tendsto rj l (𝓝 r))
    (hrj : ∀N,q (e.depth+1)≤rj N ∧ rj N≤q e.depth)
    (hrr : q (e.depth+1)≤r ∧ r≤q e.depth) :
    Tendsto (fun N => nativeStreamingEdgeVertexPairProbability D (μj N) a q T e v (rj N)) l
      (𝓝 (nativeStreamingEdgeVertexPairProbability D μ a q T e v r)) := by
  haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T) :=
    anisotropicObservationRecords_borel T
  haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T) :=
    inferInstance
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_nativeStreamingCrossVertexProbability D hμ a
      (fun N => nativeStreamingEdgeSchedule q e.depth (rj N))
      (nativeStreamingEdgeSchedule q e.depth r)
      (observationRefineTree (nativeStreamingEdgeSubdivision e.depth) T)
      (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
      (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T v)
      ?_ ?_ ?_)
  · exact (continuous_fst.fst.prodMk
      ((continuous_observationRefinementProject (nativeStreamingEdgeSubdivision e.depth) T).comp
        continuous_fst.snd)).prodMk continuous_snd
  · intro p _
    unfold nativeStreamingEdgeSchedule
    by_cases hp:p≤e.depth
    · simp only [hp,ite_true]
      exact tendsto_const_nhds
    · simp only [hp,ite_false]
      by_cases he:p=e.depth+1
      · simp only [he,ite_true]
        exact hr
      · simp only [he,ite_false]
        exact tendsto_const_nhds
  · intro N p _
    exact nativeStreamingEdgeSchedule_antitone q hq e.depth (rj N) (hrj N) (Nat.le_succ p)
  · intro p _
    exact nativeStreamingEdgeSchedule_antitone q hq e.depth r hrr (Nat.le_succ p)

end QuantitativeFollowup
