module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSameEdgeObservedLaw

@[expose] public section

/-! Exact joint ancestor selection on every pair of refined physical
edges. Shared edges use successive transitions; different branches
retain the true conditional branch product and every old record. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem nativeStreamingEdgePairSelection_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hQ : Antitone Q) (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (e f : NativeStreamingEdge T)
    (p k : ℕ) (hp : p<d e.depth) (hk : k<d f.depth) :
    (anisotropicRecordedProfileTreeKernel D μ Q (observationRefineTree d T)).map
      (nativeStreamingEdgePairSelection d e f p k)=
      nativeStreamingEdgePairObservedKernel D μ q (nativeStreamingEdgeIndexOrder p k) T e f
        (Q (observationRefinementDepth d e.depth+p+1))
        (Q (observationRefinementDepth d f.depth+k+1)) := by
  induction T generalizing p k with
  | leaf => cases e
  | @advance j T ih =>
      cases e with
      | here =>
          cases f with
          | here => exact nativeStreamingSameEdgeSelection_kernel D μ q Q d hQ hlevels T p k hp hk
          | child f =>
              rw [nativeStreamingEdgePairSelection_here_child]
              have hs : Measurable (fun z : AnisotropicObservationState n ×
                  (AnisotropicObservationState n × (AnisotropicObservationState n ×
                    Records (AnisotropicObservationState n) (Configuration n) T)) =>
                      (z.1,(z.2.2.1,(z.2.1,z.2.2.2)))) :=
                measurable_fst.prodMk (measurable_snd.snd.fst.prodMk
                  (measurable_snd.fst.prodMk measurable_snd.snd.snd))
              rw [←Function.comp_assoc,Kernel.map_comp_right _
                (measurable_nativeStreamingBlockSelectionAt _ _ p)
                (hs.comp (measurable_id.prodMap (measurable_id.prodMap
                  (measurable_nativeStreamingEdgeSelection d f k)))),
                nativeStreamingBlockSelectionAt_kernel D μ Q hQ _ _ p hp,
                Kernel.map_comp_right _ (measurable_id.prodMap (measurable_id.prodMap
                  (measurable_nativeStreamingEdgeSelection d f k))) hs,
                nativeStreaming_twoTransition_map_record _ (nativeStreamingEdgeSelection d f k)
                  (measurable_nativeStreamingEdgeSelection d f k) _ _,
                nativeStreamingEdgeSelection_kernel D μ q Q d hQ hlevels f k hk]
              rw [hlevels j,show observationRefinementDepth d j+d j+1=
                observationRefinementDepth d (j+1) from rfl,hlevels (j+1)]
              rfl
      | child e =>
          cases f with
          | here =>
              rw [nativeStreamingEdgePairSelection_child_here]
              have hs : Measurable (fun z : AnisotropicObservationState n ×
                  (AnisotropicObservationState n × (AnisotropicObservationState n ×
                    Records (AnisotropicObservationState n) (Configuration n) T)) =>
                      (z.2.2.1,(z.1,(z.2.1,z.2.2.2)))) :=
                measurable_snd.snd.fst.prodMk (measurable_fst.prodMk
                  (measurable_snd.fst.prodMk measurable_snd.snd.snd))
              rw [←Function.comp_assoc,Kernel.map_comp_right _
                (measurable_nativeStreamingBlockSelectionAt _ _ k)
                (hs.comp (measurable_id.prodMap (measurable_id.prodMap
                  (measurable_nativeStreamingEdgeSelection d e p)))),
                nativeStreamingBlockSelectionAt_kernel D μ Q hQ _ _ k hk,
                Kernel.map_comp_right _ (measurable_id.prodMap (measurable_id.prodMap
                  (measurable_nativeStreamingEdgeSelection d e p))) hs,
                nativeStreaming_twoTransition_map_record _ (nativeStreamingEdgeSelection d e p)
                  (measurable_nativeStreamingEdgeSelection d e p) _ _,
                nativeStreamingEdgeSelection_kernel D μ q Q d hQ hlevels e p hp]
              rw [hlevels j,show observationRefinementDepth d j+d j+1=
                observationRefinementDepth d (j+1) from rfl,hlevels (j+1)]
              rfl
          | child f =>
              rw [nativeStreamingEdgePairSelection_child_child]
              have hs : Measurable (fun z : AnisotropicObservationState n ×
                  (AnisotropicObservationState n × (AnisotropicObservationState n ×
                    Records (AnisotropicObservationState n) (Configuration n) T)) =>
                      (z.2.1,(z.2.2.1,(z.1,z.2.2.2)))) :=
                measurable_snd.fst.prodMk (measurable_snd.snd.fst.prodMk
                  (measurable_fst.prodMk measurable_snd.snd.snd))
              rw [←Function.comp_assoc,Kernel.map_comp_right _
                (measurable_observationBlockCollapse _ _)
                (hs.comp (measurable_id.prodMap
                  (measurable_nativeStreamingEdgePairSelection d e f p k))),
                anisotropicRecordedProfileTreeKernel_block_collapse D μ Q hQ,
                Kernel.map_comp_right _ (measurable_id.prodMap
                  (measurable_nativeStreamingEdgePairSelection d e f p k)) hs,
                Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
                  (measurable_nativeStreamingEdgePairSelection d e f p k),Kernel.map_id,
                ih e f p k hp hk]
              rw [hlevels j,show observationRefinementDepth d j+d j+1=
                observationRefinementDepth d (j+1) from rfl,hlevels (j+1)]
              rfl
  | @fork j T U ihT ihU =>
      cases e with
      | left e =>
          cases f with
          | left f =>
              rw [nativeStreamingEdgePairSelection_left_left]
              change (_ ×ₖ _).map _=_
              rw [Kernel.map_comp_right _
                ((measurable_nativeStreamingEdgePairSelection d e f p k).prodMap
                  (measurable_observationRefinementProject d U))
                (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
                  (measurable_fst.snd.snd.prodMk measurable_snd))),
                ←Kernel.map_prod_map _ _ (measurable_nativeStreamingEdgePairSelection d e f p k)
                  (measurable_observationRefinementProject d U),ihT e f p k hp hk,
                anisotropicRecordedProfileTreeKernel_refinement D μ q Q d hQ hlevels U]
              rfl
          | right f =>
              rw [nativeStreamingEdgePairSelection_left_right]
              change (_ ×ₖ _).map _=_
              rw [Kernel.map_comp_right _
                ((measurable_nativeStreamingEdgeSelection d e p).prodMap
                  (measurable_nativeStreamingEdgeSelection d f k))
                (measurable_fst.fst.prodMk (measurable_snd.fst.prodMk
                  (measurable_fst.snd.prodMk measurable_snd.snd))),
                ←Kernel.map_prod_map _ _ (measurable_nativeStreamingEdgeSelection d e p)
                  (measurable_nativeStreamingEdgeSelection d f k),
                nativeStreamingEdgeSelection_kernel D μ q Q d hQ hlevels e p hp,
                nativeStreamingEdgeSelection_kernel D μ q Q d hQ hlevels f k hk]
              rfl
      | right e =>
          cases f with
          | left f =>
              rw [nativeStreamingEdgePairSelection_right_left]
              change (_ ×ₖ _).map _=_
              rw [Kernel.map_comp_right _
                ((measurable_nativeStreamingEdgeSelection d f k).prodMap
                  (measurable_nativeStreamingEdgeSelection d e p))
                (measurable_snd.fst.prodMk (measurable_fst.fst.prodMk
                  (measurable_fst.snd.prodMk measurable_snd.snd))),
                ←Kernel.map_prod_map _ _ (measurable_nativeStreamingEdgeSelection d f k)
                  (measurable_nativeStreamingEdgeSelection d e p),
                nativeStreamingEdgeSelection_kernel D μ q Q d hQ hlevels f k hk,
                nativeStreamingEdgeSelection_kernel D μ q Q d hQ hlevels e p hp]
              rfl
          | right f =>
              rw [nativeStreamingEdgePairSelection_right_right]
              change (_ ×ₖ _).map _=_
              rw [Kernel.map_comp_right _
                ((measurable_observationRefinementProject d T).prodMap
                  (measurable_nativeStreamingEdgePairSelection d e f p k))
                (measurable_snd.fst.prodMk (measurable_snd.snd.fst.prodMk
                  (measurable_fst.prodMk measurable_snd.snd.snd))),
                ←Kernel.map_prod_map _ _ (measurable_observationRefinementProject d T)
                  (measurable_nativeStreamingEdgePairSelection d e f p k),
                anisotropicRecordedProfileTreeKernel_refinement D μ q Q d hQ hlevels T,
                ihU e f p k hp hk]
              rfl

 theorem nativeStreamingEdgePairSelection_joint_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hQ : Antitone Q) (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (e f : NativeStreamingEdge T)
    (p k : ℕ) (hp : p<d e.depth) (hk : k<d f.depth) :
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T)).map
      (Prod.map id (nativeStreamingEdgePairSelection d e f p k))=
      anisotropicObservationInitialLaw D μ a ⊗ₘ
        nativeStreamingEdgePairObservedKernel D μ q (nativeStreamingEdgeIndexOrder p k) T e f
          (Q (observationRefinementDepth d e.depth+p+1))
          (Q (observationRefinementDepth d f.depth+k+1)) := by
  rw [anisotropicRecordedProfileTreeLaw,
    ←Measure.compProd_map (measurable_nativeStreamingEdgePairSelection d e f p k),
    nativeStreamingEdgePairSelection_kernel D μ q Q d hQ hlevels T e f p k hp hk]

end QuantitativeFollowup
