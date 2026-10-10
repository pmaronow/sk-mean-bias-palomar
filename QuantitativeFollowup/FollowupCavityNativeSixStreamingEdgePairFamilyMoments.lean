module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairMomentMeasurable

@[expose] public section

/-! Terminal tests may contain the actual moving common-path clock.
The finite spin space supplies genuine test integrability; moving-law
limits retain every coefficient before the free-measure passage. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem nativeStreamingTerminalMarkMoment_abs_le_bound
    {T : FiniteTerminalGenealogy J}
    (P : ProbabilityMeasure ((AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T)×
        (Configuration n×Configuration n)))
    (G : TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (C : ℝ) (hC : ∀σ,|G σ|≤C) : |nativeStreamingTerminalMarkMoment P G|≤C := by
  simpa only [nativeStreamingTerminalMarkMoment,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=(P:Measure ((AnisotropicObservationState n×
        Records (AnisotropicObservationState n) (Configuration n) T)×
          (Configuration n×Configuration n))))
      (f := fun z => G (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
      (C := C)
      (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using
          hC (finiteCascadeRecordTerminalSpins T z.1.2,z.2))

theorem continuousOn_nativeStreamingEdgePairFixedFamilyMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T) (p k : ℕ)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hG : ∀σ,Continuous (fun z=>G z σ)) :
    ContinuousOn (fun z : Paper.Overlap×Paper.Overlap=>nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgePairProbabilityFixed D μ a q T e f p k z.1 z.2) (G z))
        (nativeStreamingEdgePairClosedSet q e f) := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_nativeStreamingMovingTerminalMarkMoment
    (tendsto_nativeStreamingEdgePairProbabilityFixed D tendsto_const_nhds a q hq T e f p k
      ((continuous_fst.comp continuous_subtype_val).tendsto z)
      ((continuous_snd.comp continuous_subtype_val).tendsto z)
      (fun w=>w.2.1) (fun w=>w.2.2) z.2.1 z.2.2)
  exact fun σ=>((hG σ).comp continuous_subtype_val).tendsto z

def nativeStreamingEdgePairFixedFamilyMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap) (p k : ℕ)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (z : Paper.Overlap×Paper.Overlap) : ℝ := by
  classical
  exact
    if nativeStreamingEdgePairOpenCondition q e f S z then
    nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgePairProbabilityFixed D μ a q T e f p k z.1 z.2) (G z) else 0

theorem measurable_nativeStreamingEdgePairFixedFamilyMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap) (p k : ℕ)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hG : ∀σ,Continuous (fun z=>G z σ)) :
    Measurable (nativeStreamingEdgePairFixedFamilyMaskedMoment D μ a q T e f S p k G) := by
  classical
  have hc := continuousOn_nativeStreamingEdgePairFixedFamilyMoment D μ a q hq T e f p k G hG
  have hsub : {z | nativeStreamingEdgePairOpenCondition q e f S z} ⊆
      nativeStreamingEdgePairClosedSet q e f := by
    intro z hz
    exact ⟨⟨hz.1.1.le,hz.1.2.1.le⟩,⟨hz.2.1.le,hz.2.2.1.le⟩⟩
  convert (hc.mono hsub).measurable_piecewise (g:=fun _=>(0:ℝ)) continuousOn_const
    (measurableSet_nativeStreamingEdgePairOpenCondition q e f S) using 1
  funext z
  by_cases hz : nativeStreamingEdgePairOpenCondition q e f S z <;>
    simp only [nativeStreamingEdgePairFixedFamilyMaskedMoment,Set.piecewise,Set.mem_setOf_eq,
      hz,ite_true,ite_false]

def nativeStreamingEdgePairFamilyMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (z : Paper.Overlap×Paper.Overlap) : ℝ := by
  classical
  exact
    if nativeStreamingEdgePairOpenCondition q e f S z then
    nativeStreamingTerminalMarkMoment (nativeStreamingEdgePairProbability D μ a q T e f z.1 z.2)
      (G z) else 0

theorem measurable_nativeStreamingEdgePairFamilyMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e f : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap×Paper.Overlap→
      TerminalSpins (Configuration n) T×(Configuration n×Configuration n)→ℝ)
    (hG : ∀σ,Continuous (fun z=>G z σ)) :
    Measurable (nativeStreamingEdgePairFamilyMaskedMoment D μ a q T e f S G) := by
  classical
  have hm p k := measurable_nativeStreamingEdgePairFixedFamilyMaskedMoment D μ a q hq T e f S p k G hG
  by_cases he : e.depth=f.depth
  · have hs₁ : MeasurableSet {z : Paper.Overlap×Paper.Overlap | z.1<z.2} :=
      measurableSet_lt measurable_fst measurable_snd
    have hs₂ : MeasurableSet {z : Paper.Overlap×Paper.Overlap | z.2<z.1} :=
      measurableSet_lt measurable_snd measurable_fst
    have hp : Measurable (fun z : Paper.Overlap×Paper.Overlap =>
        if z.1<z.2 then nativeStreamingEdgePairFixedFamilyMaskedMoment D μ a q T e f S 1 0 G z
        else if z.2<z.1 then nativeStreamingEdgePairFixedFamilyMaskedMoment D μ a q T e f S 0 1 G z
        else nativeStreamingEdgePairFixedFamilyMaskedMoment D μ a q T e f S 0 0 G z) :=
      (hm 1 0).ite hs₁ ((hm 0 1).ite hs₂ (hm 0 0))
    convert hp using 1
    funext z
    by_cases hrl : z.1<z.2
    · simp only [nativeStreamingEdgePairFamilyMaskedMoment,nativeStreamingEdgePairFixedFamilyMaskedMoment,
        nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,if_pos he,if_pos he.symm,if_pos hrl,
        if_neg (not_lt_of_gt hrl),ite_true,ite_false]
    · by_cases hlr : z.2<z.1
      · simp only [nativeStreamingEdgePairFamilyMaskedMoment,nativeStreamingEdgePairFixedFamilyMaskedMoment,
          nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,if_pos he,if_pos he.symm,if_neg hrl,if_pos hlr,ite_true,ite_false]
      · simp only [nativeStreamingEdgePairFamilyMaskedMoment,nativeStreamingEdgePairFixedFamilyMaskedMoment,
          nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,if_pos he,if_pos he.symm,if_neg hrl,if_neg hlr,ite_true,ite_false]
  · convert hm 0 0 using 1
    funext z
    simp only [nativeStreamingEdgePairFamilyMaskedMoment,nativeStreamingEdgePairFixedFamilyMaskedMoment,
      nativeStreamingEdgePairProbability,nativeStreamingPairObservationIndex,
      if_neg he,if_neg (Ne.symm he),ite_true,ite_false]

end QuantitativeFollowup
