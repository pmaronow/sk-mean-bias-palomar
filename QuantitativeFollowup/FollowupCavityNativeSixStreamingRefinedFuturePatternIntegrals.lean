module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedVertexPatternMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSelectedFuturePatternLaw

@[expose] public section

/-! A selected subdivision vertex has the complete original edge-origin
future integral. Every halfclosed future cell and upper atom is retained;
the selected and future marks may lie in the same original cell. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingPatternFutureIntegral_finite_selected_refinement
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0 ≤ a) (has : a ≤ s.m 1) (hs : s.q 1=0)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j,Q (observationRefinementDepth d j)=q j) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (p : ℕ) (hp : p<d e.depth) :
    nativeStreamingPatternFutureIntegral D (Paper.parisiSchemeMeasure s) a Q
      (observationRefineTree d T) (nativeStreamingRefinedTerminalTest d T F)
      (.vertex (nativeStreamingEdgeSelectedVertex d e p)) =
      nativeStreamingPatternFutureIntegral D (Paper.parisiSchemeMeasure s) a q T F
        (.edge e (Q (observationRefinementDepth d e.depth+p+1))) := by
  classical
  let μ := Paper.parisiSchemeMeasure s
  let ν := parisiFreeMeasure μ a
  let r := Q (observationRefinementDepth d e.depth+p+1)
  let g := fun l : Paper.Overlap => if r<l then
    (∫z,nativeStreamingDefectSpinTest (observationRefineTree d T)
      (nativeStreamingRefinedTerminalTest d T F) l
        (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2,z.2)
      ∂nativeStreamingFuturePairLaw D μ a Q (observationRefineTree d T)
        (nativeStreamingEdgeSelectedVertex d e p) l) else 0
  have hq : Antitone q := by
    intro i j hij
    rw [←hlevels i,←hlevels j]
    exact hQ ((observationRefinementDepth_strictMono d).monotone hij)
  have hQ0 : Q 0=1 := by
    simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  have h00 : Q 0=q 0 := by
    simpa only [observationRefinementDepth] using hlevels 0
  have hlow : q (e.depth+1)≤r := by
    rw [←hlevels (e.depth+1)]
    apply hQ
    simp only [observationRefinementDepth]
    omega
  have hg : Integrable g ν := by
    dsimp only [ν,μ]
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hs]
    exact integrable_vectorProfileFreeMeasure s a g
  have hcell (j : ℕ) :
      (∫l in Ioc (q (j+1)) (q j),if r<l then
        nativeStreamingPatternMoment D μ a q T F (.future (.edge e r) j l) else 0 ∂ν) =
      ∫l in Ioc (q (j+1)) (q j),g l∂ν := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
    by_cases hrl : r<l
    · have hj : j≤e.depth := by
        by_contra hh
        have H : l≤r := hl.2.trans ((hq (show e.depth+1≤j by omega)).trans hlow)
        exact (not_lt_of_ge H) hrl
      simp only [hrl,ite_true,g]
      exact (nativeStreamingSelectedFutureDefectIntegral_eq_pattern D μ a q Q d hQ
        hlevels hzero T F e p hp j hj l ⟨hl.1.le,hl.2⟩ hrl.le).symm
    · simp only [hrl,ite_false,g]
  have Hcoarse : nativeStreamingPatternFutureIntegral D μ a q T F (.edge e r) =
      ∫l in Ioc (q J) (q 0),g l∂ν := by
    unfold nativeStreamingPatternFutureIntegral
    change (∑j∈Finset.range J,∫l in Ioc (q (j+1)) (q j),if r<l then
      nativeStreamingPatternMoment D μ a q T F (.future (.edge e r) j l) else 0 ∂ν)=_
    simp_rw [hcell]
    exact nativeStreaming_setIntegral_Ioc_antitone_telescope q hq ν g hg J
  change nativeStreamingPatternFutureIntegral D μ a Q (observationRefineTree d T)
    (nativeStreamingRefinedTerminalTest d T F) (.vertex (nativeStreamingEdgeSelectedVertex d e p)) =
    nativeStreamingPatternFutureIntegral D μ a q T F (.edge e r)
  rw [nativeStreamingPatternFutureIntegral_finite_vertex D s a ha has hs Q hQ hQ0,
    hlevels J,h00,Hcoarse]
  apply integral_congr_ae
  exact .of_forall fun l => by
    rw [nativeStreamingEdgeSelectedVertex_depth d e p hp]

end QuantitativeFollowup
