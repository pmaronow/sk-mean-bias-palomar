module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairFamilyIntegral

@[expose] public section

/-! Two halfclosed edge integrations keep every upper and interior atom,
including the equal-mark diagonal. The preserved quantizer retains both
literal edge masks, and the actual complete two-ancestor law supplies
the limit before integration against the true product free measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def nativeStreamingEdgePairHalfClosedCondition (q : ℕ→Paper.Overlap)
    {T : FiniteTerminalGenealogy J} (e f : NativeStreamingEdge T)
    (z : Paper.Overlap×Paper.Overlap) : Prop :=
  (q (e.depth+1)<z.1 ∧ z.1≤q e.depth) ∧
    (q (f.depth+1)<z.2 ∧ z.2≤q f.depth)

theorem measurableSet_nativeStreamingEdgePairHalfClosedCondition (q : ℕ→Paper.Overlap)
    {T : FiniteTerminalGenealogy J} (e f : NativeStreamingEdge T) :
    MeasurableSet {z | nativeStreamingEdgePairHalfClosedCondition q e f z} := by
  exact (measurableSet_Ioc.preimage measurable_fst).inter
    (measurableSet_Ioc.preimage measurable_snd)

theorem nativeStreamingEdgePairHalfClosedCondition_preserving
    (S : Finset Paper.Overlap) (N : ℕ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (heroot : q (e.depth+1)∈S) (hechild : q e.depth∈S)
    (hfroot : q (f.depth+1)∈S) (hfchild : q f.depth∈S)
    (z : Paper.Overlap×Paper.Overlap) :
    nativeStreamingEdgePairHalfClosedCondition q e f
      (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2) ↔
      nativeStreamingEdgePairHalfClosedCondition q e f z := by
  simp only [nativeStreamingEdgePairHalfClosedCondition,
    FRSB.preservingRound_gt_iff S N z.1 _ heroot,
    FRSB.preservingRound_le_iff S N z.1 _ hechild,
    FRSB.preservingRound_gt_iff S N z.2 _ hfroot,
    FRSB.preservingRound_le_iff S N z.2 _ hfchild]

def nativeStreamingEdgePairFixedFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap) (p k : ℕ)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (z : Paper.Overlap×Paper.Overlap) : ℝ := by
  classical
  exact
    if nativeStreamingEdgePairHalfClosedCondition q e f z then
    nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgePairProbabilityFixed D μ a q T e f p k z.1 z.2) (G z) else 0

theorem measurable_nativeStreamingEdgePairFixedFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap) (p k : ℕ)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hG : ∀σ,Continuous (fun z=>G z σ)) :
    Measurable (nativeStreamingEdgePairFixedFamilyHalfClosedMoment D μ a q T e f S p k G) := by
  classical
  have hc := continuousOn_nativeStreamingEdgePairFixedFamilyMoment D μ a q hq T e f p k G hG
  have hsub : {z | nativeStreamingEdgePairHalfClosedCondition q e f z} ⊆
      nativeStreamingEdgePairClosedSet q e f := by
    intro z hz
    exact ⟨⟨hz.1.1.le,hz.1.2⟩,⟨hz.2.1.le,hz.2.2⟩⟩
  convert (hc.mono hsub).measurable_piecewise (g:=fun _=>(0:ℝ)) continuousOn_const
    (measurableSet_nativeStreamingEdgePairHalfClosedCondition q e f) using 1
  funext z
  by_cases hz : nativeStreamingEdgePairHalfClosedCondition q e f z <;>
    simp only [nativeStreamingEdgePairFixedFamilyHalfClosedMoment,Set.piecewise,Set.mem_setOf_eq,
      hz,ite_true,ite_false]

def nativeStreamingEdgePairFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (z : Paper.Overlap×Paper.Overlap) : ℝ := by
  classical
  exact
    if nativeStreamingEdgePairHalfClosedCondition q e f z then
    nativeStreamingTerminalMarkMoment (nativeStreamingEdgePairProbability D μ a q T e f z.1 z.2)
      (G z) else 0

theorem measurable_nativeStreamingEdgePairFamilyHalfClosedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hG : ∀σ,Continuous (fun z=>G z σ)) :
    Measurable (nativeStreamingEdgePairFamilyHalfClosedMoment D μ a q T e f S G) := by
  classical
  have hm p k := measurable_nativeStreamingEdgePairFixedFamilyHalfClosedMoment D μ a q hq T e f S p k G hG
  by_cases he : e.depth=f.depth
  · have hs₁ : MeasurableSet {z : Paper.Overlap×Paper.Overlap | z.1<z.2} :=
      measurableSet_lt measurable_fst measurable_snd
    have hs₂ : MeasurableSet {z : Paper.Overlap×Paper.Overlap | z.2<z.1} :=
      measurableSet_lt measurable_snd measurable_fst
    have hp : Measurable (fun z : Paper.Overlap×Paper.Overlap =>
        if z.1<z.2 then nativeStreamingEdgePairFixedFamilyHalfClosedMoment D μ a q T e f S 1 0 G z
        else if z.2<z.1 then nativeStreamingEdgePairFixedFamilyHalfClosedMoment D μ a q T e f S 0 1 G z
        else nativeStreamingEdgePairFixedFamilyHalfClosedMoment D μ a q T e f S 0 0 G z) :=
      (hm 1 0).ite hs₁ ((hm 0 1).ite hs₂ (hm 0 0))
    convert hp using 1
    funext z
    by_cases hrl : z.1<z.2
    · simp only [nativeStreamingEdgePairFamilyHalfClosedMoment,nativeStreamingEdgePairFixedFamilyHalfClosedMoment,
        nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,if_pos he,if_pos he.symm,if_pos hrl,
        if_neg (not_lt_of_gt hrl),ite_true,ite_false]
    · by_cases hlr : z.2<z.1
      · simp only [nativeStreamingEdgePairFamilyHalfClosedMoment,nativeStreamingEdgePairFixedFamilyHalfClosedMoment,
          nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,if_pos he,if_pos he.symm,if_neg hrl,if_pos hlr,ite_true,ite_false]
      · simp only [nativeStreamingEdgePairFamilyHalfClosedMoment,nativeStreamingEdgePairFixedFamilyHalfClosedMoment,
          nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,if_pos he,if_pos he.symm,if_neg hrl,if_neg hlr,ite_true,ite_false]
  · convert hm 0 0 using 1
    funext z
    simp only [nativeStreamingEdgePairFamilyHalfClosedMoment,nativeStreamingEdgePairFixedFamilyHalfClosedMoment,
      nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,
      if_neg he,if_neg (Ne.symm he),ite_true,ite_false]

theorem nativeStreamingEdgePairFamilyHalfClosedMoment_abs_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (C : ℝ) (hC : 0≤C) (hG : ∀z σ,|G z σ|≤C) (z : Paper.Overlap×Paper.Overlap) :
    |nativeStreamingEdgePairFamilyHalfClosedMoment D μ a q T e f S G z|≤C := by
  classical
  unfold nativeStreamingEdgePairFamilyHalfClosedMoment
  split_ifs
  · exact nativeStreamingTerminalMarkMoment_abs_le_bound _ (G z) C (hG z)
  · simpa only [abs_zero] using hC

theorem nativeStreamingEdgePairFamilyHalfClosedMoment_preserving_tendsto (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (heroot : q (e.depth+1)∈S) (hechild : q e.depth∈S)
    (hfroot : q (f.depth+1)∈S) (hfchild : q f.depth∈S)
    (GN : ℕ→Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hG : ∀z σ,Tendsto (fun N=>GN N
      (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2) σ) atTop (𝓝 (G z σ)))
    (z : Paper.Overlap×Paper.Overlap) :
    Tendsto (fun N=>nativeStreamingEdgePairFamilyHalfClosedMoment D (FRSB.preservingMeasure μ S N)
      a q T e f S (GN N) (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2)) atTop
        (𝓝 (nativeStreamingEdgePairFamilyHalfClosedMoment D μ a q T e f S G z)) := by
  classical
  have hm (N : ℕ) := nativeStreamingEdgePairHalfClosedCondition_preserving S N q T e f
    heroot hechild hfroot hfchild z
  by_cases hz : nativeStreamingEdgePairHalfClosedCondition q e f z
  · have hp := tendsto_nativeStreamingEdgePairMovingMoment_preserving D μ S a q hq T e f z.1 z.2
      heroot hechild hfroot hfchild ⟨hz.1.1.le,hz.1.2⟩ ⟨hz.2.1.le,hz.2.2⟩
      (fun N=>GN N (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2)) (G z) (hG z)
    simpa only [nativeStreamingEdgePairFamilyHalfClosedMoment,hm,hz,ite_true] using hp
  · simpa only [nativeStreamingEdgePairFamilyHalfClosedMoment,hm,hz,ite_false] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0))

theorem tendsto_nativeStreamingEdgePairFamilyHalfClosedFreeIntegral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e f : NativeStreamingEdge T) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (heroot : q (e.depth+1)∈S) (hechild : q e.depth∈S)
    (hfroot : q (f.depth+1)∈S) (hfchild : q f.depth∈S)
    (GN : ℕ→Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hGN : ∀N σ,Continuous (fun z=>GN N z σ))
    (hG : ∀z σ,Tendsto (fun N=>GN N
      (FRSB.preservingRound S N z.1,FRSB.preservingRound S N z.2) σ) atTop (𝓝 (G z σ)))
    (C : ℝ) (hC : 0≤C) (hbound : ∀N z σ,|GN N z σ|≤C) :
    Tendsto (fun N=>∫z,nativeStreamingEdgePairFamilyHalfClosedMoment D (FRSB.preservingMeasure μ S N)
      a q T e f S (GN N) z ∂(parisiFreeMeasure (FRSB.preservingMeasure μ S N) a).prod
        (parisiFreeMeasure (FRSB.preservingMeasure μ S N) a)) atTop
      (𝓝 (∫z,nativeStreamingEdgePairFamilyHalfClosedMoment D μ a q T e f S G z
        ∂(parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a))) :=
  nativeStreaming_free_pair_integral_tendsto μ S hzero a ha hμ _ _
    (fun N=>measurable_nativeStreamingEdgePairFamilyHalfClosedMoment D _ a q hq T e f S
      (GN N) (hGN N)) C hC
    (fun N z=>nativeStreamingEdgePairFamilyHalfClosedMoment_abs_le D _ a q T e f S
      (GN N) C hC (hbound N) z)
    (fun r l=>nativeStreamingEdgePairFamilyHalfClosedMoment_preserving_tendsto D μ a q hq T e f S
      heroot hechild hfroot hfchild GN G hG (r,l))

theorem nativeStreamingEdgePairFamilyHalfClosedIntegral_eq_Ioc
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e f : NativeStreamingEdge T) (S : Finset Paper.Overlap)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hG : ∀σ,Continuous (fun z=>G z σ))
    (C : ℝ) (hC : 0≤C) (hbound : ∀z σ,|G z σ|≤C) :
    (∫z,nativeStreamingEdgePairFamilyHalfClosedMoment D μ a q T e f S G z
      ∂(parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) =
      ∫r in Ioc (q (e.depth+1)) (q e.depth),
        ∫l in Ioc (q (f.depth+1)) (q f.depth),
          nativeStreamingTerminalMarkMoment (nativeStreamingEdgePairProbability D μ a q T e f r l)
            (G (r,l)) ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a := by
  have hi : Integrable (nativeStreamingEdgePairFamilyHalfClosedMoment D μ a q T e f S G)
      ((parisiFreeMeasure μ a).prod (parisiFreeMeasure μ a)) :=
    (integrable_const C).mono'
      (measurable_nativeStreamingEdgePairFamilyHalfClosedMoment D μ a q hq T e f S G hG).aestronglyMeasurable
      (.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using
          nativeStreamingEdgePairFamilyHalfClosedMoment_abs_le D μ a q T e f S G C hC hbound z)
  rw [integral_prod _ hi, ←integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall fun r => by
    by_cases hr : r∈Ioc (q (e.depth+1)) (q e.depth)
    · have hr' : q (e.depth+1)<r ∧ r≤q e.depth := hr
      rw [Set.indicator_of_mem hr, ←integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      exact .of_forall fun l => by
        simp only [nativeStreamingEdgePairFamilyHalfClosedMoment,
          nativeStreamingEdgePairHalfClosedCondition, hr', true_and,
          Set.indicator, mem_Ioc]
    · have hr' : ¬(q (e.depth+1)<r ∧ r≤q e.depth) := hr
      rw [Set.indicator_of_notMem hr]
      simp only [nativeStreamingEdgePairFamilyHalfClosedMoment,
        nativeStreamingEdgePairHalfClosedCondition, hr', false_and, ite_false,
        integral_zero]

end QuantitativeFollowup
