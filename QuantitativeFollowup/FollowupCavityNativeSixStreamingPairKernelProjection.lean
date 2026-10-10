module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairObservedKernel
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTwoBlockKernelCases

@[expose] public section

/-! Project the terminal records of a genuine sequential ancestral
kernel while retaining both ancestral fields and the lower field. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {X A B : Type} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]

 theorem nativeStreaming_twoTransition_map_record (K : Kernel X A) [IsSFiniteKernel K]
    (P : A → B) (hP : Measurable P) (κ₁ κ₂ : Kernel X X) [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    ((Kernel.id ×ₖ ((Kernel.id ×ₖ K) ∘ₖ κ₂)) ∘ₖ κ₁).map
      (Prod.map id (Prod.map id P))=
      (Kernel.id ×ₖ ((Kernel.id ×ₖ K.map P) ∘ₖ κ₂)) ∘ₖ κ₁ := by
  rw [Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
    (measurable_id.prodMap hP),Kernel.map_id,Kernel.map_comp,
    ←Kernel.map_prod_map _ _ measurable_id hP,Kernel.map_id]

 theorem nativeStreaming_threeTransition_map_record (K : Kernel X A) [IsSFiniteKernel K]
    (P : A → B) (hP : Measurable P) (κ₁ κ₂ κ₃ : Kernel X X)
    [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] [IsSFiniteKernel κ₃] :
    ((Kernel.id ×ₖ ((Kernel.id ×ₖ ((Kernel.id ×ₖ K) ∘ₖ κ₃)) ∘ₖ κ₂)) ∘ₖ κ₁).map
      (Prod.map id (Prod.map id (Prod.map id P)))=
      (Kernel.id ×ₖ ((Kernel.id ×ₖ ((Kernel.id ×ₖ K.map P) ∘ₖ κ₃)) ∘ₖ κ₂)) ∘ₖ κ₁ := by
  rw [Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
    (measurable_id.prodMap (measurable_id.prodMap hP)),Kernel.map_id,
    nativeStreaming_twoTransition_map_record K P hP κ₂ κ₃]

end QuantitativeFollowup
