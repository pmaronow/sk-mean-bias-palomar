module
public import QuantitativeFollowup.SupportingGeneratedOriginCrossComponentChartsGeometry
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPairObservedMarkov

@[expose] public section

/-! Padding an original component at its fixed endpoints preserves the
selected ancestral edge state and every original record jointly. The
terminal unary transition and outer root transition are true identities. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m J : ℕ}

theorem printedGeneratedEndpointLift_record_kernel
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q Q : ℕ → Paper.Overlap) (hQ : ∀j,Q (j+1)=q j) (hzero : Q 1=Q 0)
    (T : FiniteTerminalGenealogy J) :
    (anisotropicRecordedProfileTreeKernel D μ Q (observationTerminalUnaryLift T)).map
      (observationTerminalUnaryProject T) = anisotropicRecordedProfileTreeKernel D μ q T := by
  have hk : (fun j => anisotropicObservationTransition D μ (Q (j+1)) (Q j)) =
      observationTerminalUnaryKernels (fun j => anisotropicObservationTransition D μ (q (j+1)) (q j)) := by
    funext j
    cases j with
    | zero => simpa only [observationTerminalUnaryKernels,hzero] using
        anisotropicObservationTransition_same_time D μ (Q 0)
    | succ j => simp only [observationTerminalUnaryKernels,hQ]
  rw [nativeStreamingRecordedProfileTreeKernel_eq_observation,
    nativeStreamingRecordedProfileTreeKernel_eq_observation,hk]
  exact observationTreeKernel_terminalUnaryLift _ (fun _ => inferInstance) _ T

theorem printedGeneratedEndpointLift_edge_kernel
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q Q : ℕ → Paper.Overlap) (hQ : ∀j,Q (j+1)=q j) (hzero : Q 1=Q 0)
    {T : FiniteTerminalGenealogy J} (e : NativeStreamingEdge T) (r : Paper.Overlap) :
    (nativeStreamingEdgeObservedKernel D μ Q (observationTerminalUnaryLift T)
      (printedGeneratedEndpointLiftEdge e) r).map
        (Prod.map id (observationTerminalUnaryProject T)) =
      nativeStreamingEdgeObservedKernel D μ q T e r := by
  induction e with
  | @here j T =>
      change ((_ ×ₖ ((_ ×ₖ anisotropicRecordedProfileTreeKernel D μ Q
        (observationTerminalUnaryLift T)) ∘ₖ anisotropicObservationTransition D μ r (Q (j+1)))) ∘ₖ
          anisotropicObservationTransition D μ (Q (j+1+1)) r).map
        (Prod.map id (Prod.map id (observationTerminalUnaryProject T))) = _
      rw [Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
        (measurable_id.prodMap (measurable_observationTerminalUnaryProject T)),Kernel.map_id,
        Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
        (measurable_observationTerminalUnaryProject T),Kernel.map_id,
        printedGeneratedEndpointLift_record_kernel D μ q Q hQ hzero T,hQ j,hQ (j+1)]
  | @child j T e ih =>
      change (((Kernel.id ×ₖ nativeStreamingEdgeObservedKernel D μ Q (observationTerminalUnaryLift T)
        (printedGeneratedEndpointLiftEdge e) r) ∘ₖ
          anisotropicObservationTransition D μ (Q (j+1+1)) (Q (j+1))).map
        (fun z => (z.2.1,(z.1,z.2.2)))).map
          (Prod.map id (Prod.map id (observationTerminalUnaryProject T))) = _
      rw [←Kernel.map_comp_right _
        (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))
        (measurable_id.prodMap (measurable_id.prodMap (measurable_observationTerminalUnaryProject T)))]
      change ((_ ×ₖ nativeStreamingEdgeObservedKernel D μ Q (observationTerminalUnaryLift T)
        (printedGeneratedEndpointLiftEdge e) r) ∘ₖ
          anisotropicObservationTransition D μ (Q (j+1+1)) (Q (j+1))).map
        ((fun z => (z.2.1,(z.1,z.2.2))) ∘
          Prod.map id (Prod.map id (observationTerminalUnaryProject T))) = _
      rw [Kernel.map_comp_right _
        (measurable_id.prodMap (measurable_id.prodMap (measurable_observationTerminalUnaryProject T)))
        (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)),
        Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
        (measurable_id.prodMap (measurable_observationTerminalUnaryProject T)),Kernel.map_id,
        ih,hQ j,hQ (j+1)]
  | @left j T U e ih =>
      change ((nativeStreamingEdgeObservedKernel D μ Q (observationTerminalUnaryLift T)
        (printedGeneratedEndpointLiftEdge e) r ×ₖ
          anisotropicRecordedProfileTreeKernel D μ Q (observationTerminalUnaryLift U)).map
        (fun z => (z.1.1,(z.1.2,z.2)))).map
          (Prod.map id (Prod.map (observationTerminalUnaryProject T) (observationTerminalUnaryProject U))) = _
      rw [←Kernel.map_comp_right _
        (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
        (measurable_id.prodMap ((measurable_observationTerminalUnaryProject T).prodMap
          (measurable_observationTerminalUnaryProject U)))]
      change (nativeStreamingEdgeObservedKernel D μ Q (observationTerminalUnaryLift T)
        (printedGeneratedEndpointLiftEdge e) r ×ₖ
          anisotropicRecordedProfileTreeKernel D μ Q (observationTerminalUnaryLift U)).map
        ((fun z => (z.1.1,(z.1.2,z.2))) ∘
          Prod.map (Prod.map id (observationTerminalUnaryProject T))
            (observationTerminalUnaryProject U)) = _
      rw [Kernel.map_comp_right _
        ((measurable_id.prodMap (measurable_observationTerminalUnaryProject T)).prodMap
          (measurable_observationTerminalUnaryProject U))
        (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)),
        ←Kernel.map_prod_map _ _
          (measurable_id.prodMap (measurable_observationTerminalUnaryProject T))
          (measurable_observationTerminalUnaryProject U),ih,
        printedGeneratedEndpointLift_record_kernel D μ q Q hQ hzero U]
  | @right j T U e ih =>
      change ((anisotropicRecordedProfileTreeKernel D μ Q (observationTerminalUnaryLift T) ×ₖ
        nativeStreamingEdgeObservedKernel D μ Q (observationTerminalUnaryLift U)
          (printedGeneratedEndpointLiftEdge e) r).map
        (fun z => (z.2.1,(z.1,z.2.2)))).map
          (Prod.map id (Prod.map (observationTerminalUnaryProject T) (observationTerminalUnaryProject U))) = _
      rw [←Kernel.map_comp_right _
        (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))
        (measurable_id.prodMap ((measurable_observationTerminalUnaryProject T).prodMap
          (measurable_observationTerminalUnaryProject U)))]
      change (anisotropicRecordedProfileTreeKernel D μ Q (observationTerminalUnaryLift T) ×ₖ
        nativeStreamingEdgeObservedKernel D μ Q (observationTerminalUnaryLift U)
          (printedGeneratedEndpointLiftEdge e) r).map
        ((fun z => (z.2.1,(z.1,z.2.2))) ∘
          Prod.map (observationTerminalUnaryProject T)
            (Prod.map id (observationTerminalUnaryProject U))) = _
      rw [Kernel.map_comp_right _
        ((measurable_observationTerminalUnaryProject T).prodMap
          (measurable_id.prodMap (measurable_observationTerminalUnaryProject U)))
        (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)),
        ←Kernel.map_prod_map _ _ (measurable_observationTerminalUnaryProject T)
          (measurable_id.prodMap (measurable_observationTerminalUnaryProject U)),
        printedGeneratedEndpointLift_record_kernel D μ q Q hQ hzero T,ih]

theorem printedGeneratedEndpoint_edge_kernel
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (U : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (e : NativeStreamingEdge U.tree) (r : Paper.Overlap) :
    (nativeStreamingEdgeObservedKernel D μ (nativeStreamingGeneratedEndpointClock U h)
      (nativeStreamingGeneratedEndpointComponent U).tree (printedGeneratedEndpointEdge U e) r).map
        (Prod.map id (nativeStreamingGeneratedEndpointRecordProject U)) =
      nativeStreamingEdgeObservedKernel D μ (nativeStreamingGeneratedComponentClock U h) U.tree e r := by
  change (((Kernel.id ×ₖ nativeStreamingEdgeObservedKernel D μ
    (nativeStreamingGeneratedEndpointClock U h) (observationTerminalUnaryLift U.tree)
      (printedGeneratedEndpointLiftEdge e) r) ∘ₖ anisotropicObservationTransition D μ
        (nativeStreamingGeneratedEndpointClock U h (U.depth+2))
        (nativeStreamingGeneratedEndpointClock U h (U.depth+1))).map
      (fun z => (z.2.1,(z.1,z.2.2)))).map
        (Prod.map id (observationTerminalUnaryProject U.tree ∘ Prod.snd)) = _
  rw [←Kernel.map_comp_right _
    (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))
    (measurable_id.prodMap ((measurable_observationTerminalUnaryProject U.tree).comp measurable_snd))]
  change ((Kernel.id ×ₖ nativeStreamingEdgeObservedKernel D μ
    (nativeStreamingGeneratedEndpointClock U h) (observationTerminalUnaryLift U.tree)
      (printedGeneratedEndpointLiftEdge e) r) ∘ₖ anisotropicObservationTransition D μ
        (nativeStreamingGeneratedEndpointClock U h (U.depth+2))
        (nativeStreamingGeneratedEndpointClock U h (U.depth+1))).map
      ((Prod.map id (observationTerminalUnaryProject U.tree)) ∘ Prod.snd) = _
  rw [nativeStreamingGeneratedEndpointClock_duplicate_initial,
    anisotropicObservationTransition_same_time,Kernel.comp_id,
    Kernel.map_comp_right _ measurable_snd
      (measurable_id.prodMap (measurable_observationTerminalUnaryProject U.tree)),
    ←Kernel.snd_eq,Kernel.snd_prod]
  exact printedGeneratedEndpointLift_edge_kernel D μ _ _
    (nativeStreamingGeneratedEndpointClock_succ U h)
    (nativeStreamingGeneratedEndpointClock_duplicate_terminal U h) e r

theorem printedGeneratedEndpoint_edge_joint_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (e : NativeStreamingEdge U.tree) (r : Paper.Overlap) :
    (anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ
      (nativeStreamingGeneratedEndpointClock U h) (nativeStreamingGeneratedEndpointComponent U).tree
        (printedGeneratedEndpointEdge U e) r).map
      (Prod.map id (Prod.map id (nativeStreamingGeneratedEndpointRecordProject U))) =
      anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ
        (nativeStreamingGeneratedComponentClock U h) U.tree e r := by
  rw [←Measure.compProd_map
    (measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject U)),
    printedGeneratedEndpoint_edge_kernel]

end QuantitativeFollowup
