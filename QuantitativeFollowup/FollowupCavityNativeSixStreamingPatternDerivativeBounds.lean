module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternSourceResponse
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceResponseBounds

@[expose] public section

/-! One uniform, actual-model envelope for every valid first source
integrand derivative. The bound depends only on the old leaf count,
beta and the old terminal-test bound; no mark-dependent budget is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem originalSourceTest_abs_le
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C) (i k : ObservationLeaf T)
    (σ : TerminalSpins (Configuration (n+1)) T) :
    |nativeStreamingPatternOriginalTerminalTest q T F i k σ|≤2*C := by
  by_cases hik : i=k
  · simp only [nativeStreamingPatternOriginalTerminalTest,if_pos hik,abs_zero]
    positivity
  · simp only [nativeStreamingPatternOriginalTerminalTest,if_neg hik,abs_mul]
    exact (mul_le_mul (hF σ) (cavitySpinOverlapDefect_abs_le_two n _
      (q (observationCommonLevel T i k)).property _ _) (abs_nonneg _) hC).trans_eq (by ring)

theorem abs_nativeStreamingPattern_source_derivative_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (P : NativeStreamingAttachmentPattern T) (hP : nativeStreamingPatternValid q P)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    |(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F P|≤
      7*β^2*((FiniteCascadeGenealogy.leafCount (asGenealogy T)+2:ℕ):ℝ)^2*(2*C) := by
  cases P with
  | original i k =>
      exact abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
        q hq hJ hzero htop T _ _ (by omega) (2*C) (by positivity)
        (originalSourceTest_abs_le q T F C hC hF i k) u hu
  | originalFresh i o =>
      cases o with
      | vertex v =>
          apply abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
            q hq hJ hzero htop _ _ _
            (nativeStreamingPatternVertexTree_leafCount_le .single T v) (2*C) (by positivity)
            (nativeStreamingPatternVertexTerminalTest_originalFresh_abs_le T v F C hC hF i _) u hu
      | edge e r =>
          have hr := hP
          let d := nativeStreamingEdgeSubdivision e.depth
          let Q := nativeStreamingEdgeSchedule q e.depth r
          have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
          have hK : 0<observationRefinementDepth d J := by
            simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
          have hQzero : (Q 0:ℝ)=1 := by
            simpa only [Q,nativeStreamingEdgeSchedule,if_pos (Nat.zero_le _)] using hzero
          have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
            simpa only [Q,d,nativeStreamingEdgeSchedule_refinement] using htop
          apply abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
            Q hQ hK hQzero hQtop _ _ _ (nativeStreamingPatternRefinedVertexTree_leafCount_le .single d T _) (2*C) (by positivity)
            (nativeStreamingPatternRefinedVertexTerminalTest_originalFresh_abs_le d T _ F C hC hF i _) u hu
  | current o =>
      cases o with
      | vertex v =>
          exact abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
            q hq hJ hzero htop _ _ _
            (nativeStreamingPatternVertexTree_leafCount_le .current T v) (2*C) (by positivity)
            (nativeStreamingPatternVertexTerminalTest_current_abs_le T v F C hC hF _) u hu
      | edge e r =>
          have hr := hP
          let d := nativeStreamingEdgeSubdivision e.depth
          let Q := nativeStreamingEdgeSchedule q e.depth r
          have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
          have hK : 0<observationRefinementDepth d J := by
            simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
          have hQzero : (Q 0:ℝ)=1 := by
            simpa only [Q,nativeStreamingEdgeSchedule,if_pos (Nat.zero_le _)] using hzero
          have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
            simpa only [Q,d,nativeStreamingEdgeSchedule_refinement] using htop
          apply abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
            Q hQ hK hQzero hQtop _ _ _ (nativeStreamingPatternRefinedVertexTree_leafCount_le .current d T _) (2*C) (by positivity)
            (nativeStreamingPatternRefinedVertexTerminalTest_current_abs_le d T _ F C hC hF _) u hu
  | cross o p =>
      cases o with
      | vertex v =>
          cases p with
          | vertex w =>
              exact abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
                q hq hJ hzero htop _ _ _
                (le_of_eq (nativeStreamingPatternCrossTree_leafCount T v w)) (2*C) (by positivity)
                (nativeStreamingPatternCrossTerminalTest_defect_abs_le T v w F C hC hF _) u hu
          | edge e r =>
              have hr := hP.2
              let d := nativeStreamingEdgeSubdivision e.depth
              let Q := nativeStreamingEdgeSchedule q e.depth r
              have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
              have hK : 0<observationRefinementDepth d J := by
                simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
              have hQzero : (Q 0:ℝ)=1 := by
                simpa only [Q,nativeStreamingEdgeSchedule,if_pos (Nat.zero_le _)] using hzero
              have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
                simpa only [Q,d,nativeStreamingEdgeSchedule_refinement] using htop
              apply abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
                Q hQ hK hQzero hQtop _ _ _ (le_of_eq (nativeStreamingPatternRefinedCrossTree_leafCount d T _ _)) (2*C) (by positivity)
                (nativeStreamingPatternRefinedCrossTerminalTest_defect_abs_le d T _ _ F C hC hF _) u hu
      | edge e r =>
          cases p with
          | vertex v =>
              have hr := hP.1
              let d := nativeStreamingEdgeSubdivision e.depth
              let Q := nativeStreamingEdgeSchedule q e.depth r
              have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
              have hK : 0<observationRefinementDepth d J := by
                simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
              have hQzero : (Q 0:ℝ)=1 := by
                simpa only [Q,nativeStreamingEdgeSchedule,if_pos (Nat.zero_le _)] using hzero
              have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
                simpa only [Q,d,nativeStreamingEdgeSchedule_refinement] using htop
              apply abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
                Q hQ hK hQzero hQtop _ _ _ (le_of_eq (nativeStreamingPatternRefinedCrossTree_leafCount d T _ _)) (2*C) (by positivity)
                (nativeStreamingPatternRefinedCrossTerminalTest_defect_abs_le d T _ _ F C hC hF _) u hu
          | edge f l =>
              have hr := hP.1
              have hl := hP.2
              let d := nativeStreamingPairObservationSubdivision
              let Q := nativeStreamingPairObservationSchedule q e.depth f.depth r l
              have hQ : Antitone Q := nativeStreamingPairObservationSchedule_antitone q hq e.depth f.depth r l hr hl
              have hK : 0<observationRefinementDepth d J := by
                simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
              have hQzero : (Q 0:ℝ)=1 := by
                simpa only [Q,nativeStreamingPairObservationSchedule,Nat.zero_mod,Nat.zero_div,ite_true] using hzero
              have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
                simpa only [Q,d,nativeStreamingPairObservationSchedule_refinement] using htop
              apply abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
                Q hQ hK hQzero hQtop _ _ _ (le_of_eq (nativeStreamingPatternRefinedCrossTree_leafCount d T _ _)) (2*C) (by positivity)
                (nativeStreamingPatternRefinedCrossTerminalTest_defect_abs_le d T _ _ F C hC hF _) u hu
  | future o j l =>
      cases o with
      | vertex v =>
          have hl := hP.2
          let d := nativeStreamingEdgeSubdivision j
          let Q := nativeStreamingEdgeSchedule q j l
          have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq j l hl
          have hK : 0<observationRefinementDepth d J := by
            simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
          have hQzero : (Q 0:ℝ)=1 := by
            simpa only [Q,nativeStreamingEdgeSchedule,if_pos (Nat.zero_le _)] using hzero
          have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
            simpa only [Q,d,nativeStreamingEdgeSchedule_refinement] using htop
          apply abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
            Q hQ hK hQzero hQtop _ _ _ (le_of_eq (nativeStreamingPatternRefinedPairTree_leafCount d T _ _)) (2*C) (by positivity)
            (nativeStreamingPatternRefinedPairTerminalTest_defect_abs_le d T _ _ F C hC hF _) u hu
      | edge e r =>
          have hr := hP.1
          have hl := hP.2
          let d := nativeStreamingPairObservationSubdivision
          let Q := nativeStreamingPairObservationSchedule q e.depth j r l
          have hQ : Antitone Q := nativeStreamingPairObservationSchedule_antitone q hq e.depth j r l hr hl
          have hK : 0<observationRefinementDepth d J := by
            simpa only [observationRefinementDepth] using (observationRefinementDepth_strictMono d hJ)
          have hQzero : (Q 0:ℝ)=1 := by
            simpa only [Q,nativeStreamingPairObservationSchedule,Nat.zero_mod,Nat.zero_div,ite_true] using hzero
          have hQtop : (Q (observationRefinementDepth d J):ℝ)=0 := by
            simpa only [Q,d,nativeStreamingPairObservationSchedule_refinement] using htop
          apply abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
            Q hQ hK hQzero hQtop _ _ _ (le_of_eq (nativeStreamingPatternRefinedPairTree_leafCount d T _ _)) (2*C) (by positivity)
            (nativeStreamingPatternRefinedPairTerminalTest_defect_abs_le d T _ _ F C hC hF _) u hu
  | normalizer l =>
      exact abs_nativeStreamingNormalizer_source_response_le hn β ρ hβ hρ μ a ha hfloor
        q hq hJ hzero htop T F C hC hF l u hu

end QuantitativeFollowup
