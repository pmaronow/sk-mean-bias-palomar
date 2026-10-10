module
public import HexagonPaper.TreeLikelihoodEndpointRecordsBasic
public import HexagonPaper.TreeLikelihoodNative

@[expose] public section

/-! The endpoints recorded by the full-path genealogy have exactly the
native arbitrary-profile observation genealogy law. The endpoint law is
derived from the genuine path kernel, rather than supplied as a hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace HexagonPaper
open FourPapersCommon FiniteTerminalGenealogy QuantitativeFollowup SpinGlass.AT
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {X Y S : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S]

@[reducible] def treePathEndpoints (endpoint : ℕ → Y → X) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → Records Y S T → Records X S T
  | _, .leaf => id
  | _, @FiniteTerminalGenealogy.advance j T => Prod.map (endpoint j) (treePathEndpoints endpoint T)
  | _, .fork T U => Prod.map (treePathEndpoints endpoint T) (treePathEndpoints endpoint U)

theorem measurable_treePathEndpoints (endpoint : ℕ → Y → X)
    (he : ∀ j, Measurable (endpoint j)) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (treePathEndpoints (S := S) endpoint T) := by
  induction T with
  | leaf => exact measurable_id
  | @advance j T ih => exact (he j).prodMap ih
  | fork T U ihT ihU => exact ihT.prodMap ihU

@[reducible] def treeEndpointRecordKernel (leaf : Kernel X S) (edge : ℕ → Kernel X X) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → Kernel X (Records X S T)
  | _, .leaf => leaf
  | _, @FiniteTerminalGenealogy.advance j T =>
      (Kernel.id ×ₖ treeEndpointRecordKernel leaf edge T) ∘ₖ edge j
  | _, .fork T U => treeEndpointRecordKernel leaf edge T ×ₖ treeEndpointRecordKernel leaf edge U

theorem treePathRecordKernel_endpoint_records (leaf : Kernel X S)
    (edge : ℕ → Kernel X Y) (endpoint : ℕ → Y → X)
    (he : ∀ j, Measurable (endpoint j))
    [IsMarkovKernel leaf] [hEdge : ∀ j, IsMarkovKernel (edge j)]
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (treePathRecordKernel leaf edge endpoint he T).map (treePathEndpoints endpoint T) =
      treeEndpointRecordKernel leaf (fun j => (edge j).map (endpoint j)) T := by
  induction T with
  | leaf => exact Kernel.map_id leaf
  | @advance j T ih =>
      haveI := hEdge j
      haveI := isMarkovKernel_treePathRecordKernel leaf edge endpoint he inferInstance hEdge T
      change (_ ⊗ₖ _).map (Prod.map (endpoint j) (treePathEndpoints endpoint T)) = _
      rw [endpointRecord_compProd_map _ _ _ _ (he j)
        (measurable_treePathEndpoints endpoint he T), ih]
  | fork T U ihT ihU =>
      haveI := isMarkovKernel_treePathRecordKernel leaf edge endpoint he inferInstance hEdge T
      haveI := isMarkovKernel_treePathRecordKernel leaf edge endpoint he inferInstance hEdge U
      change (_ ×ₖ _).map (Prod.map (treePathEndpoints endpoint T) (treePathEndpoints endpoint U)) = _
      rw [← Kernel.map_prod_map _ _ (measurable_treePathEndpoints endpoint he T)
        (measurable_treePathEndpoints endpoint he U), ihT, ihU]

variable {n : ℕ}
theorem treeNativePathKernel_endpoint_records (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) (hq : ∀ j, q (j+1) ≤ q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (treeNativePathKernel D μ q T).map
      (treePathEndpoints (fun j => edgePathEndpoint D (q j)) T) =
        anisotropicRecordedProfileTreeKernel D μ q T := by
  rw [treeNativePathKernel, treePathRecordKernel_endpoint_records]
  have hedge : (fun j => (edgePhysicalPathKernel D μ (q (j+1)) (q j)).map
      (edgePathEndpoint D (q j))) =
      (fun j => anisotropicObservationTransition D μ (q (j+1)) (q j)) := by
    funext j
    exact edgePhysicalPathKernel_endpoint_native D μ _ _ (hq j)
  rw [hedge]
  induction T with
  | leaf => rfl
  | advance T ih => change (_ ×ₖ _) ∘ₖ _ = (_ ×ₖ _) ∘ₖ _; rw [ih]
  | fork T U ihT ihU => change _ ×ₖ _ = _ ×ₖ _; rw [ihT, ihU]

end HexagonPaper
