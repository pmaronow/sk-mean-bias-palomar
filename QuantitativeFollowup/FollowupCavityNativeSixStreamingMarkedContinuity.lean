module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMarkedLaw

@[expose] public section

/-! Weak-profile and moving-edge continuity of the complete genuine
single-mark law, with the old record and its terminal spins retained. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem nativeStreamingLinearSpin_continuous {E S:Type}
    [TopologicalSpace E] [TopologicalSpace S] (j:ℕ) :
    Continuous (observationLinearSpin (E:=E) (S:=S) j) := by
  induction j with
  | zero => exact continuous_id
  | succ j ih => exact ih.comp continuous_snd

def nativeStreamingSingleVertexProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) :
    ProbabilityMeasure ((AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T)×Configuration n) :=
  (anisotropicRecordedProfileProbability D μ a q
    (finiteCascadeContinuationGraft observationLinearTree v)).map
      (fun z=>((z.1,(finiteCascadeContinuationExtract observationLinearTree observationLinearSpin v z.2).1),
        (finiteCascadeContinuationExtract observationLinearTree observationLinearSpin v z.2).2))

theorem nativeStreamingSingleVertexProbability_eq_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (hzero : q 0=1) (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :
    (nativeStreamingSingleVertexProbability D μ a q T v:Measure _)=
      nativeStreamingSingleVertexLaw D μ a q T v := by
  exact nativeStreamingSingleVertexLaw_eq_graft D μ a q hq hzero T v

theorem tendsto_nativeStreamingSingleVertexProbability {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μj : L→Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (hμ : Tendsto μj l (𝓝 μ))
    (a : ℝ) (qj : L→ℕ→Paper.Overlap) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T)
    (hq : ∀p,p≤J→Tendsto (fun N=>qj N p) l (𝓝 (q p)))
    (hmono : ∀N,∀p,p<J→qj N (p+1)≤qj N p)
    (hMono : ∀p,p<J→q (p+1)≤q p) :
    Tendsto (fun N=>nativeStreamingSingleVertexProbability D (μj N) a (qj N) T v) l
      (𝓝 (nativeStreamingSingleVertexProbability D μ a q T v)) := by
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_anisotropicRecordedProfileProbability_moving_schedule D hμ a qj q
      (finiteCascadeContinuationGraft observationLinearTree v) hq hmono hMono)
  have he:=nativeStreamingContinuationExtract_continuous
    (E:=AnisotropicObservationState n) (S:=Configuration n)
    observationLinearTree observationLinearSpin (fun j=>nativeStreamingLinearSpin_continuous j) v
  exact (continuous_fst.prodMk (he.fst.comp continuous_snd)).prodMk (he.snd.comp continuous_snd)

theorem tendsto_nativeStreamingSingleVertexProbability_edge {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μj : L→Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (hμ : Tendsto μj l (𝓝 μ))
    (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q) (j : ℕ)
    {rj : L→Paper.Overlap} {r : Paper.Overlap} (hr : Tendsto rj l (𝓝 r))
    (hrj : ∀N,q (j+1)≤rj N ∧ rj N≤q j) (hrr : q (j+1)≤r ∧ r≤q j)
    (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree (nativeStreamingEdgeSubdivision j) T)) :
    Tendsto (fun N=>nativeStreamingSingleVertexProbability D (μj N) a
      (nativeStreamingEdgeSchedule q j (rj N))
      (observationRefineTree (nativeStreamingEdgeSubdivision j) T) v) l
      (𝓝 (nativeStreamingSingleVertexProbability D μ a (nativeStreamingEdgeSchedule q j r)
        (observationRefineTree (nativeStreamingEdgeSubdivision j) T) v)) := by
  apply tendsto_nativeStreamingSingleVertexProbability D hμ a
    (fun N=>nativeStreamingEdgeSchedule q j (rj N)) (nativeStreamingEdgeSchedule q j r) _ v
  · intro p _
    unfold nativeStreamingEdgeSchedule
    by_cases hp:p≤j
    · simp only [hp,ite_true]
      exact tendsto_const_nhds
    · simp only [hp,ite_false]
      by_cases he:p=j+1
      · simp only [he,ite_true]
        exact hr
      · simp only [he,ite_false]
        exact tendsto_const_nhds
  · intro N p _
    exact nativeStreamingEdgeSchedule_antitone q hq j (rj N) (hrj N) (Nat.le_succ p)
  · intro p _
    exact nativeStreamingEdgeSchedule_antitone q hq j r hrr (Nat.le_succ p)

end QuantitativeFollowup
