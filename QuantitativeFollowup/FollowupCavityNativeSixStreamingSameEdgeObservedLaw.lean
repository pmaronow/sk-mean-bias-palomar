module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPairKernelProjection
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairSelectionAlgebra

@[expose] public section

/-! The two selected fields on one physical edge have their genuine
successive restart law, jointly with every original record. The exact
diagonal retains one common ancestral field before terminal marking. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem nativeStreamingSameEdgeSelection_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hQ : Antitone Q) (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (p k : ℕ)
    (hp : p<d j) (hk : k<d j) :
    (anisotropicRecordedProfileTreeKernel D μ Q (observationRefineTree d (.advance T))).map
      (nativeStreamingEdgePairSelection d (.here T) (.here T) p k)=
      nativeStreamingEdgePairObservedKernel D μ q (nativeStreamingEdgeIndexOrder p k)
        (.advance T) (.here T) (.here T)
        (Q (observationRefinementDepth d j+p+1))
        (Q (observationRefinementDepth d j+k+1)) := by
  let P : Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T) →
      Records (AnisotropicObservationState n) (Configuration n) T := observationRefinementProject (E:=AnisotropicObservationState n)
    (S:=Configuration n) d T
  have hP : Measurable P := measurable_observationRefinementProject d T
  have hR : (anisotropicRecordedProfileTreeKernel D μ Q (observationRefineTree d T)).map P=
      anisotropicRecordedProfileTreeKernel D μ q T :=
    anisotropicRecordedProfileTreeKernel_refinement D μ q Q d hQ hlevels T
  have ht : observationRefinementDepth d j+d j+1=observationRefinementDepth d (j+1) := rfl
  rw [nativeStreamingEdgePairSelection_here_here]
  have hproj : Measurable (fun z : AnisotropicObservationState n ×
      (AnisotropicObservationState n × (AnisotropicObservationState n ×
        Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T))) =>
          (z.1,(z.2.1,(z.2.2.1,P z.2.2.2)))) :=
    measurable_fst.prodMk (measurable_snd.fst.prodMk
      (measurable_snd.snd.fst.prodMk (hP.comp measurable_snd.snd.snd)))
  rw [Kernel.map_comp_right _ (measurable_nativeStreamingTwoBlockSelection (observationRefineTree d T) (d j) p k) hproj]
  by_cases he : p=k
  · subst k
    rw [nativeStreamingTwoBlockSelection_kernel_eq D μ Q hQ (observationRefineTree d T) (d j) p hp]
    have hdup : Measurable (fun z : AnisotropicObservationState n ×
        (AnisotropicObservationState n × Records (AnisotropicObservationState n)
          (Configuration n) (observationRefineTree d T)) => (z.1,(z.1,z.2))) :=
      measurable_fst.prodMk (measurable_fst.prodMk measurable_snd)
    rw [←Kernel.map_comp_right _ hdup hproj]
    change Kernel.map _ ((fun z=> (z.1,(z.1,z.2))) ∘ Prod.map id (Prod.map id P))=_
    rw [Kernel.map_comp_right _ (measurable_id.prodMap (measurable_id.prodMap hP))
      (measurable_fst.prodMk (measurable_fst.prodMk measurable_snd)),
      nativeStreaming_twoTransition_map_record _ P hP _ _,hR,ht,hlevels (j+1),hlevels j]
    simp only [nativeStreamingEdgeIndexOrder,if_pos rfl,nativeStreamingEdgePairObservedKernel,
      nativeStreamingEdgeObservedKernel,ite_true,ite_false]
    rfl
  · by_cases hpk : p<k
    · rw [nativeStreamingTwoBlockSelection_kernel_lt D μ Q hQ (observationRefineTree d T) (d j) p k hpk hk]
      have hs : Measurable (fun z : AnisotropicObservationState n ×
          (AnisotropicObservationState n × (AnisotropicObservationState n ×
            Records (AnisotropicObservationState n) (Configuration n) (observationRefineTree d T))) =>
              (z.2.1,(z.1,z.2.2))) :=
        measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)
      rw [←Kernel.map_comp_right _ hs hproj]
      change Kernel.map _ ((fun z=> (z.2.1,(z.1,z.2.2))) ∘
        Prod.map id (Prod.map id (Prod.map id P)))=_
      rw [Kernel.map_comp_right _
        (measurable_id.prodMap (measurable_id.prodMap (measurable_id.prodMap hP)))
        (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)),
        nativeStreaming_threeTransition_map_record _ P hP _ _ _,hR,ht,hlevels (j+1),hlevels j]
      simp only [nativeStreamingEdgeIndexOrder,if_neg he,if_pos hpk,
        nativeStreamingEdgePairObservedKernel,ite_true,ite_false]
      rfl
    · have hkp : k<p := by omega
      rw [nativeStreamingTwoBlockSelection_kernel_gt D μ Q hQ (observationRefineTree d T) (d j) p k hkp hp]
      change Kernel.map _ (Prod.map id (Prod.map id (Prod.map id P)))=_
      rw [nativeStreaming_threeTransition_map_record _ P hP _ _ _,hR,ht,hlevels (j+1),hlevels j]
      simp only [nativeStreamingEdgeIndexOrder,if_neg he,if_neg hpk,
        nativeStreamingEdgePairObservedKernel,ite_true,ite_false]
      rfl

end QuantitativeFollowup
