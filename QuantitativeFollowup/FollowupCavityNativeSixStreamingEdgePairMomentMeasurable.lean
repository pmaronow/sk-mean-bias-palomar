module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairPreservingLimit

@[expose] public section

/-! Genuine two-ancestor spin moments are Borel functions of both marks.
The two-slot realization is continuous for each fixed pair of indices;
the canonical ordering is a finite measurable case split. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

 def nativeStreamingEdgePairClosedSet (q : ℕ→Paper.Overlap)
    {T : FiniteTerminalGenealogy J} (e f : NativeStreamingEdge T) :
    Set (Paper.Overlap×Paper.Overlap) :=
  {z | z.1∈Icc (q (e.depth+1)) (q e.depth) ∧
    z.2∈Icc (q (f.depth+1)) (q f.depth)}

 theorem continuousOn_nativeStreamingEdgePairFixedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T) (p k : ℕ)
    (G : TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ) :
    ContinuousOn (fun z : Paper.Overlap×Paper.Overlap=>nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgePairProbabilityFixed D μ a q T e f p k z.1 z.2) G)
        (nativeStreamingEdgePairClosedSet q e f) := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_nativeStreamingTerminalMarkMoment
  exact tendsto_nativeStreamingEdgePairProbabilityFixed D tendsto_const_nhds a q hq T e f p k
    ((continuous_fst.comp continuous_subtype_val).tendsto z)
    ((continuous_snd.comp continuous_subtype_val).tendsto z)
    (fun w=>w.2.1) (fun w=>w.2.2) z.2.1 z.2.2

 def nativeStreamingEdgePairOpenCondition (q : ℕ→Paper.Overlap)
    {T : FiniteTerminalGenealogy J} (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap) (z : Paper.Overlap×Paper.Overlap) : Prop :=
  (q (e.depth+1)<z.1 ∧ z.1<q e.depth ∧ z.1∉S) ∧
    (q (f.depth+1)<z.2 ∧ z.2<q f.depth ∧ z.2∉S)

 theorem measurableSet_nativeStreamingEdgePairOpenCondition (q : ℕ→Paper.Overlap)
    {T : FiniteTerminalGenealogy J} (e f : NativeStreamingEdge T) (S : Finset Paper.Overlap) :
    MeasurableSet {z | nativeStreamingEdgePairOpenCondition q e f S z} := by
  have he : MeasurableSet {r : Paper.Overlap | q (e.depth+1)<r ∧ r<q e.depth ∧ r∉S}:=
    isOpen_Ioi.measurableSet.inter (isOpen_Iio.measurableSet.inter S.finite_toSet.measurableSet.compl)
  have hf : MeasurableSet {r : Paper.Overlap | q (f.depth+1)<r ∧ r<q f.depth ∧ r∉S}:=
    isOpen_Ioi.measurableSet.inter (isOpen_Iio.measurableSet.inter S.finite_toSet.measurableSet.compl)
  exact (he.preimage measurable_fst).inter (hf.preimage measurable_snd)

 def nativeStreamingEdgePairFixedMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap) (p k : ℕ)
    (G : TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (z : Paper.Overlap×Paper.Overlap) : ℝ := by
  classical
  exact
    if nativeStreamingEdgePairOpenCondition q e f S z then
    nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgePairProbabilityFixed D μ a q T e f p k z.1 z.2) G else 0

 theorem measurable_nativeStreamingEdgePairFixedMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap) (p k : ℕ)
    (G : TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ) :
    Measurable (nativeStreamingEdgePairFixedMaskedMoment D μ a q T e f S p k G) := by
  classical
  have hc := continuousOn_nativeStreamingEdgePairFixedMoment D μ a q hq T e f p k G
  have hsub : {z | nativeStreamingEdgePairOpenCondition q e f S z} ⊆
      nativeStreamingEdgePairClosedSet q e f := by
    intro z hz
    exact ⟨⟨hz.1.1.le,hz.1.2.1.le⟩,⟨hz.2.1.le,hz.2.2.1.le⟩⟩
  convert (hc.mono hsub).measurable_piecewise (g:=fun _=>(0:ℝ)) continuousOn_const
    (measurableSet_nativeStreamingEdgePairOpenCondition q e f S) using 1
  funext z
  by_cases hz : nativeStreamingEdgePairOpenCondition q e f S z <;>
    simp only [nativeStreamingEdgePairFixedMaskedMoment,Set.piecewise,Set.mem_setOf_eq,
      hz,ite_true,ite_false]

 def nativeStreamingEdgePairMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (z : Paper.Overlap×Paper.Overlap) : ℝ := by
  classical
  exact
    if nativeStreamingEdgePairOpenCondition q e f S z then
    nativeStreamingTerminalMarkMoment (nativeStreamingEdgePairProbability D μ a q T e f z.1 z.2) G
  else 0

 theorem measurable_nativeStreamingEdgePairMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ) :
    Measurable (nativeStreamingEdgePairMaskedMoment D μ a q T e f S G) := by
  classical
  have hm p k := measurable_nativeStreamingEdgePairFixedMaskedMoment D μ a q hq T e f S p k G
  by_cases he : e.depth=f.depth
  · have hs₁ : MeasurableSet {z : Paper.Overlap×Paper.Overlap | z.1<z.2} :=
      measurableSet_lt measurable_fst measurable_snd
    have hs₂ : MeasurableSet {z : Paper.Overlap×Paper.Overlap | z.2<z.1} :=
      measurableSet_lt measurable_snd measurable_fst
    have hp : Measurable (fun z : Paper.Overlap×Paper.Overlap =>
        if z.1<z.2 then nativeStreamingEdgePairFixedMaskedMoment D μ a q T e f S 1 0 G z
        else if z.2<z.1 then nativeStreamingEdgePairFixedMaskedMoment D μ a q T e f S 0 1 G z
        else nativeStreamingEdgePairFixedMaskedMoment D μ a q T e f S 0 0 G z) :=
      (hm 1 0).ite hs₁ ((hm 0 1).ite hs₂ (hm 0 0))
    convert hp using 1
    funext z
    by_cases hrl : z.1<z.2
    · simp only [nativeStreamingEdgePairMaskedMoment,nativeStreamingEdgePairFixedMaskedMoment,
        nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,if_pos he,if_pos he.symm,if_pos hrl,
        if_neg (not_lt_of_gt hrl),ite_true,ite_false]
    · by_cases hlr : z.2<z.1
      · simp only [nativeStreamingEdgePairMaskedMoment,nativeStreamingEdgePairFixedMaskedMoment,
          nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,if_pos he,if_pos he.symm,if_neg hrl,if_pos hlr,ite_true,ite_false]
      · simp only [nativeStreamingEdgePairMaskedMoment,nativeStreamingEdgePairFixedMaskedMoment,
          nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,if_pos he,if_pos he.symm,if_neg hrl,if_neg hlr,ite_true,ite_false]
  · convert hm 0 0 using 1
    funext z
    simp only [nativeStreamingEdgePairMaskedMoment,nativeStreamingEdgePairFixedMaskedMoment,
      nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,
      if_neg he,if_neg (Ne.symm he),ite_true,ite_false]

end QuantitativeFollowup
