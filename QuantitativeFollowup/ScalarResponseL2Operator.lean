module
public import QuantitativeFollowup.ScalarResponseLinear
public import QuantitativeFollowup.ScalarResponseSymmetry
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-! The actual endpoint-compressed response on the paper's completed
Hilbert space, extended from the genuine dense endpoint-fixed tests. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def scalarResponseL2Operator (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    endpointFixedL2 (parisiFreeMeasure μ a)→L[ℝ]endpointFixedL2 (parisiFreeMeasure μ a) :=
  (scalarResponseTestLinearMap β hβ μ a ha hμ).extendOfNorm
    (endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a))

theorem scalarResponseL2Operator_test (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (φ : endpointFixedLipschitzTests) :
    scalarResponseL2Operator β hβ μ a ha hμ (endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) φ)=
      scalarResponseTestLinearMap β hβ μ a ha hμ φ :=
  LinearMap.extendOfNorm_eq (endpointFixedLipschitzLinearEmbedding_denseRange _) ⟨scalarResponseL2Bound β,scalarResponseTestLinearMap_norm_le β hβ μ a ha hμ⟩ φ

theorem scalarResponseL2Operator_norm_le (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    ‖scalarResponseL2Operator β hβ μ a ha hμ‖ ≤ scalarResponseL2Bound β :=
  LinearMap.opNorm_extendOfNorm_le (endpointFixedLipschitzLinearEmbedding_denseRange _)
    (scalarResponseL2Bound_nonneg β) (scalarResponseTestLinearMap_norm_le β hβ μ a ha hμ)

theorem scalarResponseL2Operator_test_coeFn (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (φ : endpointFixedLipschitzTests) :
    (scalarResponseL2Operator β hβ μ a ha hμ (endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) φ) : Lp ℝ 2 (parisiFreeMeasure μ a))=ᵐ[parisiFreeMeasure μ a]
      scalarCompressedResponse β hβ μ a φ.val := by
  rw [scalarResponseL2Operator_test]
  change (endpointFixedL2Compression (parisiFreeMeasure μ a) (ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ (scalarResponseContinuousMap β hβ a ha φ.val ⟨μ,hμ⟩)) : Lp ℝ 2 (parisiFreeMeasure μ a))=ᵐ[parisiFreeMeasure μ a] _
  filter_upwards [endpointFixedL2Compression_coeFn (parisiFreeMeasure μ a) (ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ (scalarResponseContinuousMap β hβ a ha φ.val ⟨μ,hμ⟩)),
    (scalarResponseContinuousMap β hβ a ha φ.val ⟨μ,hμ⟩).coeFn_toLp (p:=2) (μ:=parisiFreeMeasure μ a) (𝕜:=ℝ)] with q hq hφ
  rw [hq]
  by_cases he : q∈overlapEndpointSet
  · simp only [endpointInteriorIndicator,indicator_of_notMem (show q∉overlapEndpointSetᶜ from fun h=>h he)]
    exact (ite_eq_left he).symm
  · simp only [endpointInteriorIndicator,indicator_of_mem (show q∈overlapEndpointSetᶜ from he),hφ]
    exact (ite_eq_right he).symm

theorem scalarResponseL2Operator_test_pairing (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (φ ψ : endpointFixedLipschitzTests) :
    inner ℝ (endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) φ)
      (scalarResponseL2Operator β hβ μ a ha hμ (endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) ψ))=
      ∫q : Paper.Overlap,φ.val q*scalarResponseOperator β hβ μ a ψ.val q ∂parisiFreeMeasure μ a := by
  rw [scalarResponseL2Operator_test]
  change inner ℝ (ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ φ.val)
    (endpointFixedL2Compression (parisiFreeMeasure μ a) (ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ (scalarResponseContinuousMap β hβ a ha ψ.val ⟨μ,hμ⟩))).val=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [φ.val.coeFn_toLp (p:=2) (μ:=parisiFreeMeasure μ a) (𝕜:=ℝ),
    endpointFixedL2Compression_coeFn (parisiFreeMeasure μ a) (ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ (scalarResponseContinuousMap β hβ a ha ψ.val ⟨μ,hμ⟩)),
    (scalarResponseContinuousMap β hβ a ha ψ.val ⟨μ,hμ⟩).coeFn_toLp (p:=2) (μ:=parisiFreeMeasure μ a) (𝕜:=ℝ)] with q hφ hJ hψ
  change inner ℝ ((ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ φ.val) q)
    ((endpointFixedL2Compression (parisiFreeMeasure μ a) (ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ (scalarResponseContinuousMap β hβ a ha ψ.val ⟨μ,hμ⟩))).val q)=_
  rw [hφ,hJ]
  by_cases he : q∈overlapEndpointSet
  · have hz : φ.val q=0 := by
      rcases he with hq|hq
      · have hq' : q=zeroOverlap := Subtype.ext hq
        rw [hq'];exact φ.property.1
      · have hq' : q=(1:Paper.Overlap) := Subtype.ext hq
        rw [hq'];exact φ.property.2.1
    simp [endpointInteriorIndicator,he,hz]
  · simp only [endpointInteriorIndicator,indicator_of_mem (show q∈overlapEndpointSetᶜ from he),hψ,RCLike.inner_apply,conj_trivial]
    change scalarResponseOperator β hβ μ a ψ.val q*φ.val q=φ.val q*scalarResponseOperator β hβ μ a ψ.val q
    ring

theorem scalarResponseL2Operator_test_symmetric (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (φ ψ : endpointFixedLipschitzTests) :
    inner ℝ (scalarResponseL2Operator β hβ.ne' μ a ha hμ (endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) φ))
      (endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) ψ)=
      inner ℝ (endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) φ)
        (scalarResponseL2Operator β hβ.ne' μ a ha hμ (endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) ψ)) := by
  rw [real_inner_comm,scalarResponseL2Operator_test_pairing,scalarResponseL2Operator_test_pairing]
  obtain ⟨Lφ,hφ⟩:=φ.property.2.2
  obtain ⟨Lψ,hψ⟩:=ψ.property.2.2
  exact (scalar_response_pairing_symmetric β hβ μ a ha hμ φ.val ψ.val Lφ Lψ hφ hψ φ.property.1 φ.property.2.1 ψ.property.1 ψ.property.2.1).symm

theorem scalarResponseL2Operator_isSelfAdjoint (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    IsSelfAdjoint (scalarResponseL2Operator β hβ.ne' μ a ha hμ) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro f g
  let e := endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a)
  let J := scalarResponseL2Operator β hβ.ne' μ a ha hμ
  have hd : DenseRange e := endpointFixedLipschitzLinearEmbedding_denseRange _
  refine hd.induction_on₂ (p:=fun f g=>inner ℝ (J f) g=inner ℝ f (J g)) ?_ ?_ f g
  · exact isClosed_eq ((J.continuous.comp continuous_fst).inner continuous_snd)
      (continuous_fst.inner (J.continuous.comp continuous_snd))
  · intro φ ψ
    exact scalarResponseL2Operator_test_symmetric β hβ μ a ha hμ φ ψ

end QuantitativeFollowup
