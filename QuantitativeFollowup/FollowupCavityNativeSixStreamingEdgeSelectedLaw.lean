module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelection

@[expose] public section

/-! The selected interior state and every original genealogical record
have their genuine native two-transition law.  This identifies hidden
ancestral states jointly, rather than identifying only terminal-spin
marginals. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def nativeStreamingEdgeObservedKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → NativeStreamingEdge T →
      Paper.Overlap → Kernel (AnisotropicObservationState n)
        (AnisotropicObservationState n × Records (AnisotropicObservationState n) (Configuration n) T)
  | _, _, @NativeStreamingEdge.here j T, r =>
      (Kernel.id ×ₖ ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) ∘ₖ
        anisotropicObservationTransition D μ r (q j))) ∘ₖ
          anisotropicObservationTransition D μ (q (j+1)) r
  | _, _, @NativeStreamingEdge.child j T e, r =>
      ((Kernel.id ×ₖ nativeStreamingEdgeObservedKernel D μ q T e r) ∘ₖ
        anisotropicObservationTransition D μ (q (j+1)) (q j)).map
          (fun z => (z.2.1,(z.1,z.2.2)))
  | _, _, @NativeStreamingEdge.left j T U e, r =>
      (nativeStreamingEdgeObservedKernel D μ q T e r ×ₖ
        anisotropicRecordedProfileTreeKernel D μ q U).map
          (fun z => (z.1.1,(z.1.2,z.2)))
  | _, _, @NativeStreamingEdge.right j T U e, r =>
      (anisotropicRecordedProfileTreeKernel D μ q T ×ₖ
        nativeStreamingEdgeObservedKernel D μ q U e r).map
          (fun z => (z.2.1,(z.1,z.2.2)))

theorem nativeStreamingEdgeSelection_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hQ : Antitone Q) (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) :
    (anisotropicRecordedProfileTreeKernel D μ Q (observationRefineTree d T)).map
      (nativeStreamingEdgeSelection d e p)=
      nativeStreamingEdgeObservedKernel D μ q T e
        (Q (observationRefinementDepth d e.depth+p+1)) := by
  induction e with
  | @here j T =>
      change (anisotropicRecordedProfileTreeKernel D μ Q
        (.advance (observationTreePad (observationRefineTree d T) (d j)))).map
        (Prod.map id (Prod.map id (observationRefinementProject d T)) ∘
          nativeStreamingBlockSelectionAt (observationRefineTree d T) (d j) p)=_
      rw [Kernel.map_comp_right _ (measurable_nativeStreamingBlockSelectionAt _ _ p)
        (measurable_id.prodMap (measurable_id.prodMap (measurable_observationRefinementProject d T))),
        nativeStreamingBlockSelectionAt_kernel D μ Q hQ _ _ p hp,
        Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
          (measurable_id.prodMap (measurable_observationRefinementProject d T)),Kernel.map_id,
        Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
          (measurable_observationRefinementProject d T),Kernel.map_id,
        anisotropicRecordedProfileTreeKernel_refinement D μ q Q d hQ hlevels T]
      rw [hlevels j,show observationRefinementDepth d j+d j+1=
        observationRefinementDepth d (j+1) from rfl,hlevels (j+1)]
  | @child j T e ih =>
      change (anisotropicRecordedProfileTreeKernel D μ Q
        (.advance (observationTreePad (observationRefineTree d T) (d j)))).map
        ((fun z => (z.2.1,(z.1,z.2.2))) ∘
          (Prod.map id (nativeStreamingEdgeSelection d e p)) ∘
            observationBlockCollapse (observationRefineTree d T) (d j))=_
      rw [←Function.comp_assoc]
      rw [Kernel.map_comp_right _ (measurable_observationBlockCollapse _ _)
          ((measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)).comp
            (measurable_id.prodMap (measurable_nativeStreamingEdgeSelection d e p))),
        anisotropicRecordedProfileTreeKernel_block_collapse D μ Q hQ,
        Kernel.map_comp_right _
          (measurable_id.prodMap (measurable_nativeStreamingEdgeSelection d e p))
          (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)),
        Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
          (measurable_nativeStreamingEdgeSelection d e p),Kernel.map_id,ih hp]
      rw [hlevels j,show observationRefinementDepth d j+d j+1=
        observationRefinementDepth d (j+1) from rfl,hlevels (j+1)]
  | @left j T U e ih =>
      change (_ ×ₖ _).map ((fun z => (z.1.1,(z.1.2,z.2))) ∘
        Prod.map (nativeStreamingEdgeSelection d e p) (observationRefinementProject d U))=_
      rw [Kernel.map_comp_right _
          ((measurable_nativeStreamingEdgeSelection d e p).prodMap
            (measurable_observationRefinementProject d U))
          (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)),
        ←Kernel.map_prod_map _ _ (measurable_nativeStreamingEdgeSelection d e p)
          (measurable_observationRefinementProject d U),ih hp,
        anisotropicRecordedProfileTreeKernel_refinement D μ q Q d hQ hlevels U]
  | @right j T U e ih =>
      change (_ ×ₖ _).map ((fun z => (z.2.1,(z.1,z.2.2))) ∘
        Prod.map (observationRefinementProject d T) (nativeStreamingEdgeSelection d e p))=_
      rw [Kernel.map_comp_right _
          ((measurable_observationRefinementProject d T).prodMap
            (measurable_nativeStreamingEdgeSelection d e p))
          (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)),
        ←Kernel.map_prod_map _ _ (measurable_observationRefinementProject d T)
          (measurable_nativeStreamingEdgeSelection d e p),
        anisotropicRecordedProfileTreeKernel_refinement D μ q Q d hQ hlevels T,ih hp]

theorem nativeStreamingEdgeSelection_joint_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hQ : Antitone Q) (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) :
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T)).map
      (Prod.map id (nativeStreamingEdgeSelection d e p))=
      anisotropicObservationInitialLaw D μ a ⊗ₘ
        nativeStreamingEdgeObservedKernel D μ q T e
          (Q (observationRefinementDepth d e.depth+p+1)) := by
  rw [anisotropicRecordedProfileTreeLaw,
    ←Measure.compProd_map (measurable_nativeStreamingEdgeSelection d e p),
    nativeStreamingEdgeSelection_kernel D μ q Q d hQ hlevels e p hp]

end QuantitativeFollowup
