module
public import QuantitativeFollowup.FollowupCavityRestResponseTrace

@[expose] public section

/-! The scalar response acts on arbitrary continuous random rest paths in
L², by the proved all-continuous L² bound and actual dense extension. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityScalarFullResponseTests (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    C(Paper.Overlap,ℝ)→ₗ[ℝ]Lp ℝ 2 (parisiFreeMeasure μ a) :=
  (ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ).toLinearMap.comp
    (scalarResponseContinuousLinearMap β hβ μ a ha hμ)

 theorem cavityScalarFullResponseTests_norm_le (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (φ : C(Paper.Overlap,ℝ)) :
    ‖cavityScalarFullResponseTests β hβ μ a ha hμ φ‖≤
      scalarResponseL2Bound β*‖ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ φ‖ :=
  scalar_response_L2_bound β hβ μ a ha hμ φ

def cavityScalarFullResponseL2 (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    Lp ℝ 2 (parisiFreeMeasure μ a)→L[ℝ]Lp ℝ 2 (parisiFreeMeasure μ a) :=
  (cavityScalarFullResponseTests β hβ μ a ha hμ).extendOfNorm
    (ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ).toLinearMap

 theorem cavityScalarFullResponseL2_continuous_test (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (φ : C(Paper.Overlap,ℝ)) :
    cavityScalarFullResponseL2 β hβ μ a ha hμ (ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ φ)=
      ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ
        (scalarResponseContinuousMap β hβ a ha φ ⟨μ,hμ⟩) :=
  LinearMap.extendOfNorm_eq (ContinuousMap.toLp_denseRange (p:=2) (μ:=parisiFreeMeasure μ a) ℝ ℝ (by norm_num))
    ⟨scalarResponseL2Bound β,cavityScalarFullResponseTests_norm_le β hβ μ a ha hμ⟩ φ

 theorem cavityScalarFullResponseL2_compression (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    (endpointFixedL2Compression (parisiFreeMeasure μ a)).comp
      ((cavityScalarFullResponseL2 β hβ μ a ha hμ).comp (endpointFixedL2 (parisiFreeMeasure μ a)).subtypeL)=
      scalarResponseL2Operator β hβ μ a ha hμ := by
  let ν:=parisiFreeMeasure μ a
  let J:=(endpointFixedL2Compression ν).comp
    ((cavityScalarFullResponseL2 β hβ μ a ha hμ).comp (endpointFixedL2 ν).subtypeL)
  let K:=scalarResponseL2Operator β hβ μ a ha hμ
  let e:=endpointFixedLipschitzLinearEmbedding ν
  apply ContinuousLinearMap.ext
  intro f
  refine (endpointFixedLipschitzLinearEmbedding_denseRange ν).induction_on
    (p:=fun f=>J f=K f) f ?_ ?_
  · exact isClosed_eq J.continuous K.continuous
  · intro φ
    rw [show K (e φ)=scalarResponseTestLinearMap β hβ μ a ha hμ φ from
      scalarResponseL2Operator_test β hβ μ a ha hμ φ]
    change endpointFixedL2Compression ν
      (cavityScalarFullResponseL2 β hβ μ a ha hμ (ContinuousMap.toLp 2 ν ℝ φ.val))=_
    rw [cavityScalarFullResponseL2_continuous_test]
    rfl

 theorem scalarResponseL2Operator_continuous_pairing (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (φ : C(Paper.Overlap,ℝ)) (hφ : ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ φ∈
      endpointFixedL2 (parisiFreeMeasure μ a)) :
    inner ℝ (⟨ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ φ,hφ⟩ :
        endpointFixedL2 (parisiFreeMeasure μ a))
      (scalarResponseL2Operator β hβ μ a ha hμ ⟨ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ φ,hφ⟩)=
      ∫p : Paper.Overlap,φ p*scalarResponseOperator β hβ μ a φ p ∂parisiFreeMeasure μ a := by
  let ν:=parisiFreeMeasure μ a
  rw [←cavityScalarFullResponseL2_compression]
  change inner ℝ (ContinuousMap.toLp 2 ν ℝ φ)
    ((endpointFixedL2Compression ν (cavityScalarFullResponseL2 β hβ μ a ha hμ
      (ContinuousMap.toLp 2 ν ℝ φ))).val)=_
  rw [cavityScalarFullResponseL2_continuous_test,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp (p:=2) (μ:=ν) (𝕜:=ℝ),
    endpointFixedL2Compression_coeFn ν (ContinuousMap.toLp 2 ν ℝ
      (scalarResponseContinuousMap β hβ a ha φ ⟨μ,hμ⟩)),
    (scalarResponseContinuousMap β hβ a ha φ ⟨μ,hμ⟩).coeFn_toLp (p:=2) (μ:=ν) (𝕜:=ℝ),
    (mem_endpointFixedL2_iff ν _).mp hφ] with p h1 h2 h3 h4
  change inner ℝ ((ContinuousMap.toLp 2 ν ℝ φ) p)
    ((endpointFixedL2Compression ν (ContinuousMap.toLp 2 ν ℝ
      (scalarResponseContinuousMap β hβ a ha φ ⟨μ,hμ⟩))).val p)=_
  rw [h2]
  by_cases he : p∈overlapEndpointSet
  · have hz : φ p=0 := by rw [←h1];exact h4 he
    simp [endpointInteriorIndicator,he,hz]
  · rw [endpointInteriorIndicator,indicator_of_mem (show p∈overlapEndpointSetᶜ from he),h1,h3]
    change scalarResponseOperator β hβ μ a φ p*φ p=φ p*scalarResponseOperator β hβ μ a φ p
    ring

end QuantitativeFollowup
