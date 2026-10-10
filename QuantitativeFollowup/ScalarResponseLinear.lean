module
public import QuantitativeFollowup.ScalarResponseL2Bounds
public import FourPapersCommon.EndpointFixedL2Compression
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

/-! Linearity of the literal scalar response, using its proved continuous
regrouped kernel representation and genuine finite-measure integrability. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem scalarResponsePsi1_add (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ ψ : C(Paper.Overlap,ℝ)) (p r : Paper.Overlap) :
    scalarResponsePsi1 β μ (φ+ψ) p r = scalarResponsePsi1 β μ φ p r + scalarResponsePsi1 β μ ψ p r := by
  unfold scalarResponsePsi1
  simp only [ContinuousMap.add_apply]
  split_ifs <;> ring

theorem scalarResponsePsi2_add (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ ψ : C(Paper.Overlap,ℝ)) (p r ell : Paper.Overlap) :
    scalarResponsePsi2 β μ (φ+ψ) p r ell = scalarResponsePsi2 β μ φ p r ell + scalarResponsePsi2 β μ ψ p r ell := by
  unfold scalarResponsePsi2
  simp only [ContinuousMap.add_apply]
  split_ifs <;> ring

theorem scalarResponsePsi1_smul (β : ℝ) (μ : Paper.ParisiMeasure)
    (c : ℝ) (φ : C(Paper.Overlap,ℝ)) (p r : Paper.Overlap) :
    scalarResponsePsi1 β μ (c • φ) p r = c*scalarResponsePsi1 β μ φ p r := by
  unfold scalarResponsePsi1
  simp only [ContinuousMap.smul_apply,smul_eq_mul]
  split_ifs <;> ring

theorem scalarResponsePsi2_smul (β : ℝ) (μ : Paper.ParisiMeasure)
    (c : ℝ) (φ : C(Paper.Overlap,ℝ)) (p r ell : Paper.Overlap) :
    scalarResponsePsi2 β μ (c • φ) p r ell = c*scalarResponsePsi2 β μ φ p r ell := by
  unfold scalarResponsePsi2
  simp only [ContinuousMap.smul_apply,smul_eq_mul]
  split_ifs <;> ring

theorem integrable_scalarResponsePsi1 (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (φ : C(Paper.Overlap,ℝ)) (p : Paper.Overlap) :
    Integrable (fun r=>scalarResponsePsi1 β μ φ p r) (parisiFreeMeasure μ a) := by
  have h : Continuous (fun r : Paper.Overlap=>scalarResponsePsi1 β μ φ p r) := by
    convert! (continuous_scalarResponsePsi1 β hβ φ).comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)) using 1
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_scalarResponsePsi2 (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (φ : C(Paper.Overlap,ℝ)) (p r : Paper.Overlap) :
    Integrable (fun ell=>scalarResponsePsi2 β μ φ p r ell) (parisiFreeMeasure μ a) := by
  have h : Continuous (fun ell : Paper.Overlap=>scalarResponsePsi2 β μ φ p r ell) := by
    convert! (continuous_scalarResponsePsi2 β hβ φ).comp
      (continuous_const.prodMk (continuous_const.prodMk (continuous_const.prodMk continuous_id))) using 1
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_scalarResponsePsi2_integral (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (φ : C(Paper.Overlap,ℝ)) (p : Paper.Overlap) :
    Integrable (fun r=>∫ell,scalarResponsePsi2 β μ φ p r ell ∂parisiFreeMeasure μ a) (parisiFreeMeasure μ a) := by
  have h : Continuous (fun z : Paper.Overlap×Paper.Overlap=>scalarResponsePsi2 β μ φ p z.1 z.2) := by
    convert! (continuous_scalarResponsePsi2 β hβ φ).comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)) using 1
  exact (h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).integral_prod_left

theorem scalarRegroupedResponse_add (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (φ ψ : C(Paper.Overlap,ℝ)) (p : Paper.Overlap) :
    scalarRegroupedResponse β μ a (φ+ψ) p=scalarRegroupedResponse β μ a φ p+scalarRegroupedResponse β μ a ψ p := by
  unfold scalarRegroupedResponse
  simp only [scalarResponsePsi1_add,scalarResponsePsi2_add,ContinuousMap.add_apply]
  simp_rw [integral_add (integrable_scalarResponsePsi2 β hβ μ a φ p _) (integrable_scalarResponsePsi2 β hβ μ a ψ p _)]
  rw [integral_add (integrable_scalarResponsePsi1 β hβ μ a φ p) (integrable_scalarResponsePsi1 β hβ μ a ψ p),
    integral_add (integrable_scalarResponsePsi2_integral β hβ μ a φ p) (integrable_scalarResponsePsi2_integral β hβ μ a ψ p)]
  ring

theorem scalarRegroupedResponse_smul (β : ℝ) (μ : Paper.ParisiMeasure)
    (a c : ℝ) (φ : C(Paper.Overlap,ℝ)) (p : Paper.Overlap) :
    scalarRegroupedResponse β μ a (c • φ) p=c*scalarRegroupedResponse β μ a φ p := by
  unfold scalarRegroupedResponse
  simp only [scalarResponsePsi1_smul,scalarResponsePsi2_smul,ContinuousMap.smul_apply,smul_eq_mul]
  simp_rw [integral_const_mul]
  ring

def scalarResponseContinuousLinearMap (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    C(Paper.Overlap,ℝ)→ₗ[ℝ]C(Paper.Overlap,ℝ) where
  toFun φ := scalarResponseContinuousMap β hβ a ha φ ⟨μ,hμ⟩
  map_add' φ ψ := by
    ext p
    change scalarResponseOperator β hβ μ a (φ+ψ) p=scalarResponseOperator β hβ μ a φ p+scalarResponseOperator β hβ μ a ψ p
    calc
      _=scalarRegroupedResponse β μ a (φ+ψ) p:=scalarResponseOperator_eq_regrouped β hβ μ a ha hμ (φ+ψ) p
      _=scalarRegroupedResponse β μ a φ p+scalarRegroupedResponse β μ a ψ p:=scalarRegroupedResponse_add β hβ μ a φ ψ p
      _=_:=congrArg₂ (·+·) (scalarResponseOperator_eq_regrouped β hβ μ a ha hμ φ p).symm
        (scalarResponseOperator_eq_regrouped β hβ μ a ha hμ ψ p).symm
  map_smul' c φ := by
    ext p
    change scalarResponseOperator β hβ μ a (c • φ) p=c*scalarResponseOperator β hβ μ a φ p
    calc
      _=scalarRegroupedResponse β μ a (c • φ) p:=scalarResponseOperator_eq_regrouped β hβ μ a ha hμ (c • φ) p
      _=c*scalarRegroupedResponse β μ a φ p:=scalarRegroupedResponse_smul β μ a c φ p
      _=_:=congrArg (c*·) (scalarResponseOperator_eq_regrouped β hβ μ a ha hμ φ p).symm

def scalarResponseTestLinearMap (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    endpointFixedLipschitzTests→ₗ[ℝ]endpointFixedL2 (parisiFreeMeasure μ a) :=
  (endpointFixedL2Compression (parisiFreeMeasure μ a)).toLinearMap.comp
    ((ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ).toLinearMap.comp
      ((scalarResponseContinuousLinearMap β hβ μ a ha hμ).comp endpointFixedLipschitzTests.subtype))

theorem scalarResponseTestLinearMap_norm_le (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (φ : endpointFixedLipschitzTests) :
    ‖scalarResponseTestLinearMap β hβ μ a ha hμ φ‖ ≤ scalarResponseL2Bound β*‖endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) φ‖ := by
  exact (endpointFixedL2Compression_norm_le _ _).trans (scalar_response_L2_bound β hβ μ a ha hμ φ.val)

end QuantitativeFollowup
