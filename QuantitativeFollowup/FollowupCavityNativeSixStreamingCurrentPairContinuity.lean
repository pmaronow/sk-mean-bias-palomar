module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCurrentPairLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeMarkLaw

@[expose] public section

/-! Actual current two-fresh-spin laws, at original vertices and at
inserted ancestral edge states, converge jointly with the whole old
genealogy.  The pair is drawn from the genuine conditional product kernel. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

def nativeStreamingCurrentPairProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :=
  nativeStreamingActualContinuationProbability D μ a q nativeStreamingCurrentPairTree
    nativeStreamingCurrentPairExtract T v

theorem nativeStreamingCurrentPairProbability_eq_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (hzero : q 0=1) (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :
    (nativeStreamingCurrentPairProbability D μ a q T v : Measure _)=
      nativeStreamingCurrentPairLaw D μ a q T v := by
  change (anisotropicRecordedProfileTreeLaw D μ a q _).map _=_
  exact nativeStreamingCurrentPairLaw_eq_graft D μ a q hq hzero T v

theorem tendsto_nativeStreamingCurrentPairProbability
    {L : Type*} {l : Filter L} [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μj : L → Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (hμ : Tendsto μj l (𝓝 μ))
    (a : ℝ) (qj : L → ℕ → Paper.Overlap) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T)
    (hq : ∀p,p≤J → Tendsto (fun N => qj N p) l (𝓝 (q p)))
    (hmono : ∀N,∀p,p<J → qj N (p+1)≤qj N p)
    (hMono : ∀p,p<J → q (p+1)≤q p) :
    Tendsto (fun N => nativeStreamingCurrentPairProbability D (μj N) a (qj N) T v) l
      (𝓝 (nativeStreamingCurrentPairProbability D μ a q T v)) :=
  tendsto_nativeStreamingActualContinuationProbability D hμ a qj q
    nativeStreamingCurrentPairTree nativeStreamingCurrentPairExtract
    (fun j => nativeStreamingCurrentPairExtract_continuous j) T v hq hmono hMono

def nativeStreamingEdgeCurrentPairProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (r : Paper.Overlap) :=
  (nativeStreamingCurrentPairProbability D μ a (nativeStreamingEdgeSchedule q e.depth r)
    (observationRefineTree (nativeStreamingEdgeSubdivision e.depth) T)
    (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)).map
      (fun z => ((z.1.1,observationRefinementProject (nativeStreamingEdgeSubdivision e.depth)
        T z.1.2),z.2))

theorem tendsto_nativeStreamingEdgeCurrentPairProbability
    {L : Type*} {l : Filter L} [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μj : L → Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (hμ : Tendsto μj l (𝓝 μ))
    (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    {rj : L → Paper.Overlap} {r : Paper.Overlap} (hr : Tendsto rj l (𝓝 r))
    (hrj : ∀N,q (e.depth+1)≤rj N ∧ rj N≤q e.depth)
    (hrr : q (e.depth+1)≤r ∧ r≤q e.depth) :
    Tendsto (fun N => nativeStreamingEdgeCurrentPairProbability D (μj N) a q T e (rj N)) l
      (𝓝 (nativeStreamingEdgeCurrentPairProbability D μ a q T e r)) := by
  haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T) :=
    anisotropicObservationRecords_borel T
  haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T) :=
    inferInstance
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_nativeStreamingCurrentPairProbability D hμ a
      (fun N => nativeStreamingEdgeSchedule q e.depth (rj N))
      (nativeStreamingEdgeSchedule q e.depth r)
      (observationRefineTree (nativeStreamingEdgeSubdivision e.depth) T)
      (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e)
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
