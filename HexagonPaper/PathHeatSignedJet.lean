module
public import HexagonPaper.PathHeatSignedContractions
public import HexagonPaper.PathHeatBernstein
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.NormedSpace

@[expose] public section

/-! Actual continuous linear derivative forms represented by signed measures.
The jet hypotheses below are derivatives of a path functional, not a Gaussian
expectation or a Price formula. Pullbacks apply to the actual finite sampling
map as soon as it is a continuous linear map. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]

-- Use the topology/additive/module fields of one consistent native normed
-- structure. This prevents a compact-open/operator-topology instance diamond
-- when the codomain is itself a space of continuous linear maps.
local instance instSignedJetPathNormed : NormedAddCommGroup C(X,ℝ) := inferInstance
local instance instSignedJetPathSpace : NormedSpace ℝ C(X,ℝ) := inferInstance
local instance instSignedJetPathTopo : TopologicalSpace C(X,ℝ) :=
  instSignedJetPathNormed.toUniformSpace.toTopologicalSpace
local instance instSignedJetPathAdd : AddCommGroup C(X,ℝ) := instSignedJetPathNormed.toAddCommGroup
local instance instSignedJetPathMod : Module ℝ C(X,ℝ) := instSignedJetPathSpace.toModule
local instance instSignedJetDualNormed : NormedAddCommGroup (C(X,ℝ)→L[ℝ]ℝ) := inferInstance
local instance instSignedJetDualSpace : NormedSpace ℝ (C(X,ℝ)→L[ℝ]ℝ) := inferInstance
local instance instSignedJetDualTopo : TopologicalSpace (C(X,ℝ)→L[ℝ]ℝ) :=
  instSignedJetDualNormed.toUniformSpace.toTopologicalSpace
local instance instSignedJetDualAdd : AddCommGroup (C(X,ℝ)→L[ℝ]ℝ) :=
  instSignedJetDualNormed.toAddCommGroup
local instance instSignedJetDualMod : Module ℝ (C(X,ℝ)→L[ℝ]ℝ) := instSignedJetDualSpace.toModule

theorem pathHeat_continuous_integrable (f : C(X,ℝ)) (S : SignedMeasure X) :
    Integrable f S.variation :=
  (BoundedContinuousFunction.mkOfCompact f).integrable S.variation

def pathHeatSignedScoreLinear (S : SignedMeasure X) : C(X,ℝ)→ₗ[ℝ]ℝ where
  toFun h := ∫ᵛx,h x ∂•S
  map_add' h k := VectorMeasure.integral_fun_add
    (pathHeat_continuous_integrable h S) (pathHeat_continuous_integrable k S)
  map_smul' c h := VectorMeasure.integral_fun_smul S (ContinuousLinearMap.lsmul ℝ ℝ) c h

theorem pathHeatSignedScore_bound (S : SignedMeasure X) (h : C(X,ℝ)) :
    ‖pathHeatSignedScoreLinear S h‖≤signedTV S*‖h‖ := by
  have hb := VectorMeasure.norm_integral_le_of_norm_le_const
    (B:=ContinuousLinearMap.lsmul ℝ ℝ) (μ:=S) (f:=fun x=>h x)
    (Filter.Eventually.of_forall (fun x=>h.norm_coe_le_norm x))
  simpa [pathHeatSignedScoreLinear,signedTV,mul_comm] using hb

def pathHeatSignedScore (S : SignedMeasure X) : C(X,ℝ)→L[ℝ]ℝ :=
  (pathHeatSignedScoreLinear S).mkContinuous (signedTV S) (pathHeatSignedScore_bound S)

@[simp] theorem pathHeatSignedScore_apply (S : SignedMeasure X) (h : C(X,ℝ)) :
    pathHeatSignedScore S h=∫ᵛx,h x ∂•S := rfl

theorem norm_pathHeatSignedScore_le (S : SignedMeasure X) :
    ‖pathHeatSignedScore S‖≤signedTV S :=
  LinearMap.mkContinuous_norm_le _ (signedTV_nonneg S) (pathHeatSignedScore_bound S)

def pathHeatTensor (h k : C(X,ℝ)) : C(X×X,ℝ) :=
  ⟨fun x=>h x.1*k x.2,(h.continuous.comp continuous_fst).mul (k.continuous.comp continuous_snd)⟩

def pathHeatTensorLinear : C(X,ℝ)→ₗ[ℝ]C(X,ℝ)→ₗ[ℝ]C(X×X,ℝ) :=
  LinearMap.mk₂ ℝ pathHeatTensor
    (by intro h g k;ext x;simp [pathHeatTensor,add_mul])
    (by intro c h k;ext x;simp [pathHeatTensor,mul_assoc])
    (by intro h k g;ext x;simp [pathHeatTensor,mul_add])
    (by intro c h k;ext x;simp [pathHeatTensor,mul_left_comm])

theorem norm_pathHeatTensor_le (h k : C(X,ℝ)) :
    ‖pathHeatTensor h k‖≤‖h‖*‖k‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg h) (norm_nonneg k))).mpr
  intro x
  exact (norm_mul_le (h x.1) (k x.2)).trans
    (mul_le_mul (h.norm_coe_le_norm x.1) (k.norm_coe_le_norm x.2) (norm_nonneg _) (norm_nonneg _))

def pathHeatTensorCLM : C(X,ℝ)→L[ℝ]C(X,ℝ)→L[ℝ]C(X×X,ℝ) :=
  pathHeatTensorLinear.mkContinuous₂ 1 (by
    intro h k
    simpa only [pathHeatTensorLinear,LinearMap.mk₂_apply,one_mul] using norm_pathHeatTensor_le h k)

@[simp] theorem pathHeatTensorCLM_apply (h k : C(X,ℝ)) :
    pathHeatTensorCLM h k=pathHeatTensor h k := rfl

def pathHeatSignedHessian (M : SignedMeasure (X×X)) : C(X,ℝ)→L[ℝ]C(X,ℝ)→L[ℝ]ℝ :=
  (ContinuousLinearMap.compL ℝ C(X,ℝ) C(X×X,ℝ) ℝ (pathHeatSignedScore M)).comp pathHeatTensorCLM

@[simp] theorem pathHeatSignedHessian_apply (M : SignedMeasure (X×X)) (h k : C(X,ℝ)) :
    pathHeatSignedHessian M h k=∫ᵛx,h x.1*k x.2 ∂•M := rfl

theorem norm_pathHeatSignedHessian_le (M : SignedMeasure (X×X)) :
    ‖pathHeatSignedHessian M‖≤signedTV M := by
  apply (pathHeatSignedHessian M).opNorm_le_bound (signedTV_nonneg M)
  intro h
  apply (pathHeatSignedHessian M h).opNorm_le_bound (mul_nonneg (signedTV_nonneg M) (norm_nonneg h))
  intro k
  have hb := pathHeatSignedScore_bound M (pathHeatTensor h k)
  exact hb.trans ((mul_le_mul_of_nonneg_left (norm_pathHeatTensor_le h k)
    (signedTV_nonneg M)).trans_eq (by ring))

theorem pathHeatSignedScore_sub (S T : SignedMeasure X) :
    pathHeatSignedScore (S-T)=pathHeatSignedScore S-pathHeatSignedScore T := by
  ext h
  exact VectorMeasure.integral_sub_vectorMeasure
    (pathHeat_continuous_integrable h S) (pathHeat_continuous_integrable h T)

theorem pathHeatSignedHessian_sub (M N : SignedMeasure (X×X)) :
    pathHeatSignedHessian (M-N)=pathHeatSignedHessian M-pathHeatSignedHessian N := by
  ext h k
  exact VectorMeasure.integral_sub_vectorMeasure
    (pathHeat_continuous_integrable (pathHeatTensor h k) M)
    (pathHeat_continuous_integrable (pathHeatTensor h k) N)

theorem norm_pathHeatSignedScore_sub_le (S T : SignedMeasure X) :
    ‖pathHeatSignedScore S-pathHeatSignedScore T‖≤signedTV (S-T) := by
  rw [←pathHeatSignedScore_sub]
  exact norm_pathHeatSignedScore_le _

theorem norm_pathHeatSignedHessian_sub_le (M N : SignedMeasure (X×X)) :
    ‖pathHeatSignedHessian M-pathHeatSignedHessian N‖≤signedTV (M-N) := by
  rw [←pathHeatSignedHessian_sub]
  exact norm_pathHeatSignedHessian_le _

theorem tendsto_pathHeatSignedScore {ι : Type*} {l : Filter ι}
    (S : ι→SignedMeasure X) (T : SignedMeasure X)
    (h : Tendsto (fun i=>signedTV (S i-T)) l (𝓝 0)) :
    Tendsto (fun i=>pathHeatSignedScore (S i)) l (𝓝 (pathHeatSignedScore T)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h.eventually (Iio_mem_nhds hε)] with i hi
  rw [dist_eq_norm]
  exact (norm_pathHeatSignedScore_sub_le _ _).trans_lt hi

theorem tendsto_pathHeatSignedHessian {ι : Type*} {l : Filter ι}
    (M : ι→SignedMeasure (X×X)) (N : SignedMeasure (X×X))
    (h : Tendsto (fun i=>signedTV (M i-N)) l (𝓝 0)) :
    Tendsto (fun i=>pathHeatSignedHessian (M i)) l (𝓝 (pathHeatSignedHessian N)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h.eventually (Iio_mem_nhds hε)] with i hi
  rw [dist_eq_norm]
  exact (norm_pathHeatSignedHessian_sub_le _ _).trans_lt hi

theorem contDiff_two_of_pathHeatSignedJets (f : C(X,ℝ)→ℝ)
    (S : C(X,ℝ)→SignedMeasure X) (M : C(X,ℝ)→SignedMeasure (X×X))
    (hf : ∀p,HasFDerivAt f (pathHeatSignedScore (S p)) p)
    (hS : ∀p,HasFDerivAt (fun q=>pathHeatSignedScore (S q)) (pathHeatSignedHessian (M p)) p)
    (hM : ∀p,Tendsto (fun q=>signedTV (M q-M p)) (𝓝 p) (𝓝 0)) :
    ContDiff ℝ 2 f := by
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨fun p=>pathHeatSignedScore (S p),?_,hf⟩
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun p=>pathHeatSignedHessian (M p),?_,hS⟩
  exact continuous_iff_continuousAt.mpr (fun p=>tendsto_pathHeatSignedHessian M (M p) (hM p))

end HexagonPaper
