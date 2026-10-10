module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeFutureFamilyMoments

@[expose] public section
/-! The strict-future pair law retains the complete original record.
Its moving finite-spin moments are measurable on each actual edge cell. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def nativeStreamingEdgeFutureHalfClosedCondition (q : ℕ→Paper.Overlap)
    {T : FiniteTerminalGenealogy J} (e : NativeStreamingEdge T) (j : ℕ)
    (S : Finset Paper.Overlap) (z : Paper.Overlap×Paper.Overlap) : Prop :=
  (q (e.depth+1)<z.1 ∧ z.1≤q e.depth) ∧
    (q (j+1)<z.2 ∧ z.2≤q j) ∧ z.1<z.2

theorem measurableSet_nativeStreamingEdgeFutureHalfClosedCondition (q : ℕ→Paper.Overlap)
    {T : FiniteTerminalGenealogy J} (e : NativeStreamingEdge T) (j : ℕ)
    (S : Finset Paper.Overlap) :
    MeasurableSet {z | nativeStreamingEdgeFutureHalfClosedCondition q e j S z} := by
  have he : MeasurableSet {r : Paper.Overlap | q (e.depth+1)<r ∧ r≤q e.depth} :=
    measurableSet_Ioc
  have hf : MeasurableSet {r : Paper.Overlap | q (j+1)<r ∧ r≤q j} :=
    measurableSet_Ioc
  have hlt : MeasurableSet {z : Paper.Overlap × Paper.Overlap | z.1 < z.2} :=
    measurableSet_lt measurable_fst measurable_snd
  exact (he.preimage measurable_fst).inter ((hf.preimage measurable_snd).inter hlt)

def nativeStreamingEdgeFutureFixedFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (j : ℕ)
    (S : Finset Paper.Overlap) (p k : ℕ)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (z : Paper.Overlap×Paper.Overlap) : ℝ := by
  classical
  exact if nativeStreamingEdgeFutureHalfClosedCondition q e j S z then
    nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgeFutureProbabilityFixed D μ a q T e j p k z.1 z.2) (G z) else 0

theorem measurable_nativeStreamingEdgeFutureFixedFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (j : ℕ)
    (S : Finset Paper.Overlap) (p k : ℕ)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hG : ∀σ,Continuous (fun z=>G z σ)) :
    Measurable (nativeStreamingEdgeFutureFixedFamilyHalfClosedMoment D μ a q T e j S p k G) := by
  classical
  have hc := continuousOn_nativeStreamingEdgeFutureFixedFamilyMoment D μ a q hq T e j p k G hG
  have hsub : {z | nativeStreamingEdgeFutureHalfClosedCondition q e j S z} ⊆
      nativeStreamingEdgeFutureClosedSet q e j := by
    intro z hz
    exact ⟨⟨hz.1.1.le,hz.1.2⟩,⟨hz.2.1.1.le,hz.2.1.2⟩⟩
  convert (hc.mono hsub).measurable_piecewise (g:=fun _=>(0:ℝ)) continuousOn_const
    (measurableSet_nativeStreamingEdgeFutureHalfClosedCondition q e j S) using 1
  funext z
  by_cases hz : nativeStreamingEdgeFutureHalfClosedCondition q e j S z <;>
    simp only [nativeStreamingEdgeFutureFixedFamilyHalfClosedMoment,Set.piecewise,
      Set.mem_setOf_eq,hz,ite_true,ite_false]

def nativeStreamingEdgeFutureFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (j : ℕ)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (z : Paper.Overlap×Paper.Overlap) : ℝ := by
  classical
  exact if nativeStreamingEdgeFutureHalfClosedCondition q e j S z then
    nativeStreamingTerminalMarkMoment (nativeStreamingEdgeFutureProbability D μ a q T e j z.1 z.2)
      (G z) else 0

theorem measurable_nativeStreamingEdgeFutureFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (j : ℕ)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hG : ∀σ,Continuous (fun z=>G z σ)) :
    Measurable (nativeStreamingEdgeFutureFamilyHalfClosedMoment D μ a q T e j S G) := by
  classical
  by_cases he : e.depth=j
  · convert measurable_nativeStreamingEdgeFutureFixedFamilyHalfClosedMoment D μ a q hq T e j S
      1 0 G hG using 1
    funext z
    by_cases hz : nativeStreamingEdgeFutureHalfClosedCondition q e j S z
    · have hrl : z.1<z.2 := hz.2.2
      simp only [nativeStreamingEdgeFutureFamilyHalfClosedMoment,nativeStreamingEdgeFutureFixedFamilyHalfClosedMoment,
        nativeStreamingEdgeFutureProbability,nativeStreamingPairObservationIndex,if_pos he,if_pos he.symm,hz,if_pos hrl,
        if_neg (not_lt_of_gt hrl),ite_true,ite_false]
    · simp only [nativeStreamingEdgeFutureFamilyHalfClosedMoment,
        nativeStreamingEdgeFutureFixedFamilyHalfClosedMoment,hz,ite_false]
  · convert measurable_nativeStreamingEdgeFutureFixedFamilyHalfClosedMoment D μ a q hq T e j S
      0 0 G hG using 1
    funext z
    simp only [nativeStreamingEdgeFutureFamilyHalfClosedMoment,nativeStreamingEdgeFutureFixedFamilyHalfClosedMoment,
      nativeStreamingEdgeFutureProbability,nativeStreamingPairObservationIndex,if_neg he,
      if_neg (Ne.symm he),ite_true,ite_false]

end QuantitativeFollowup
