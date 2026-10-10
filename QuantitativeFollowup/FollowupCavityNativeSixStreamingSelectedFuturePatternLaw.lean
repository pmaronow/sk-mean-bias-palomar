module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeFutureEndpoint
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinementTerminalMoments

@[expose] public section

/-! A selected subdivision field and its shared future continuation have
the original edge-origin law, retaining the complete old record and both
fresh terminal spins.  Equal cells and repeated physical clocks are kept. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingSelectedFutureLaw_eq_origin
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) (j : ℕ) (hj : j≤e.depth) (l : Paper.Overlap)
    (hl : q (j+1)≤l ∧ l≤q j)
    (hrl : Q (observationRefinementDepth d e.depth+p+1)≤l) :
    (nativeStreamingFuturePairLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) l).map
        (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2)) =
      (nativeStreamingOriginFutureProbability D μ a q T
        (.edge e (Q (observationRefinementDepth d e.depth+p+1))) j l : Measure _) := by
  let r := Q (observationRefinementDepth d e.depth+p+1)
  have hq : Antitone q := by
    intro i k hik
    rw [←hlevels i,←hlevels k]
    exact hQ ((observationRefinementDepth_strictMono d).monotone hik)
  have hlow : observationRefinementDepth d e.depth≤
      observationRefinementDepth d e.depth+p+1 := by omega
  have hupp : observationRefinementDepth d e.depth+p+1≤
      observationRefinementDepth d (e.depth+1) := by
    simp only [observationRefinementDepth]
    omega
  have hr : q (e.depth+1)≤r ∧ r≤q e.depth := by
    constructor
    · rw [←hlevels (e.depth+1)]
      exact hQ hupp
    · rw [←hlevels e.depth]
      exact hQ hlow
  let ps := nativeStreamingPairObservationIndex e.depth j r l
  let ks := nativeStreamingPairObservationIndex j e.depth l r
  have hps : ps<2 := nativeStreamingPairObservationIndex_lt _ _ _ _
  have hfuture : observationRefinementDepth nativeStreamingPairObservationSubdivision j+ks+1≤
      observationRefinementDepth nativeStreamingPairObservationSubdivision e.depth+ps+1 :=
    nativeStreamingPairObservationIndex_future_le e.depth j r l hj hrl
  have hpr : nativeStreamingPairObservationSchedule q e.depth j r l
      (observationRefinementDepth nativeStreamingPairObservationSubdivision e.depth+ps+1)=r :=
    nativeStreamingPairObservationIndex_level q e.depth j r l
  have hkl : nativeStreamingPairObservationSchedule q e.depth j r l
      (observationRefinementDepth nativeStreamingPairObservationSubdivision j+ks+1)=l :=
    nativeStreamingPairObservationIndex_second_level q e.depth j r l
  have H := nativeStreamingEdgeFutureProbabilityFixed_eq_kernel D μ a q hq hzero
    T e j ps ks hps hfuture r l hr hl
  rw [hpr,hkl] at H
  have Hproj := nativeStreamingEdgeSelectedFutureLaw_projection D μ a q Q d hQ
    hlevels e p hp l
  change (nativeStreamingFuturePairLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) l).map
        (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2)) =
    (nativeStreamingEdgeFutureProbabilityFixed D μ a q T e j ps ks r l : Measure _)
  exact Hproj.trans H.symm

theorem nativeStreamingSelectedFutureTerminalIntegral_eq_origin
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) (j : ℕ) (hj : j≤e.depth) (l : Paper.Overlap)
    (hl : q (j+1)≤l ∧ l≤q j)
    (hrl : Q (observationRefinementDepth d e.depth+p+1)≤l)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    (∫z,G (observationRefinementTerminalProject d T rfl
        (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2),z.2)
      ∂nativeStreamingFuturePairLaw D μ a Q (observationRefineTree d T)
        (nativeStreamingEdgeSelectedVertex d e p) l) =
      nativeStreamingTerminalMarkMoment
        (nativeStreamingOriginFutureProbability D μ a q T
          (.edge e (Q (observationRefinementDepth d e.depth+p+1))) j l) G := by
  have hm : Measurable (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n)
        (observationRefineTree d T)) × (Configuration n × Configuration n)) =>
      ((z.1.1,observationRefinementProject d T z.1.2),z.2)) :=
    (measurable_fst.fst.prodMk
      ((measurable_observationRefinementProject d T).comp measurable_fst.snd)).prodMk measurable_snd
  have hG : Measurable (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
        (Configuration n × Configuration n)) =>
      G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (measurable_of_finite G).comp
      (((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_fst.snd).prodMk measurable_snd)
  have he := integral_map (μ:=nativeStreamingFuturePairLaw D μ a Q
      (observationRefineTree d T) (nativeStreamingEdgeSelectedVertex d e p) l)
    hm.aemeasurable hG.aestronglyMeasurable
  rw [nativeStreamingSelectedFutureLaw_eq_origin D μ a q Q d hQ hlevels hzero
    T e p hp j hj l hl hrl] at he
  simpa only [nativeStreamingTerminalMarkMoment,Function.comp_def,
    nativeStreamingRefinementTerminalProject_record] using he.symm

theorem nativeStreamingSelectedFutureDefectIntegral_eq_pattern
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (p : ℕ) (hp : p<d e.depth)
    (j : ℕ) (hj : j≤e.depth) (l : Paper.Overlap)
    (hl : q (j+1)≤l ∧ l≤q j)
    (hrl : Q (observationRefinementDepth d e.depth+p+1)≤l) :
    (∫z,nativeStreamingRefinedTerminalTest d T F
        (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2) *
          cavitySpinOverlapDefect n l z.2.1 z.2.2
      ∂nativeStreamingFuturePairLaw D μ a Q (observationRefineTree d T)
        (nativeStreamingEdgeSelectedVertex d e p) l) =
      nativeStreamingPatternMoment D μ a q T F
        (.future (.edge e (Q (observationRefinementDepth d e.depth+p+1))) j l) := by
  simpa only [nativeStreamingRefinedTerminalTest,Function.comp_apply,
    nativeStreamingDefectSpinTest,nativeStreamingPatternMoment] using
    nativeStreamingSelectedFutureTerminalIntegral_eq_origin D μ a q Q d hQ hlevels hzero
      T e p hp j hj l hl hrl (nativeStreamingDefectSpinTest T F l)

end QuantitativeFollowup
