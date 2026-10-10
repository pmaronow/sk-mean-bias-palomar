module
public import HexagonPaper.PathHeatBrownianMesh
public import HexagonPaper.PathHeatClockFactorLaw

@[expose] public section

/-! Canonical reindexing of genuine independent Wiener mesh observations.
The reindexing is an actual continuous linear map with its actual mapped law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators
namespace HexagonPaper
open Paper FourPapersCommon QuantitativePaper QuantitativeFollowup
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {j n : ℕ}

def pathHeatWienerMeshReindex :
    pathHeatWienerMeshField (Fin j) (n+1) →L[ℝ] QuantitativePaper.Field (j*(n+1)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (j*(n+1)) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun p : Fin (j*(n+1)) =>
      PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin j × Fin (n+1) => ℝ) (finProdFinEquiv.symm p))

@[simp] theorem pathHeatWienerMeshReindex_apply
    (x : pathHeatWienerMeshField (Fin j) (n+1)) (p : Fin (j*(n+1))) :
    pathHeatWienerMeshReindex x p = x (finProdFinEquiv.symm p) := rfl

def pathHeatWienerMeshReindexedLaw (c : Fin j → Fin (n+1) → Paper.Overlap) :
    Measure (QuantitativePaper.Field (j*(n+1))) :=
  (pathHeatWienerMeshLaw c).map pathHeatWienerMeshReindex

instance pathHeatWienerMeshReindexedLaw_isGaussian
    (c : Fin j → Fin (n+1) → Paper.Overlap) :
    IsGaussian (pathHeatWienerMeshReindexedLaw c) := by
  unfold pathHeatWienerMeshReindexedLaw
  infer_instance

theorem pathHeatWienerMeshReindexedLaw_eq_actual_map
    (c : Fin j → Fin (n+1) → Paper.Overlap) :
    pathHeatWienerMeshReindexedLaw c =
      (pathHeatWienerMeshBase (J:=Fin j)).map
        (fun w => pathHeatWienerMeshReindex (pathHeatWienerMeshSample c w)) := by
  rw [pathHeatWienerMeshReindexedLaw,pathHeatWienerMeshLaw,Measure.map_map
    pathHeatWienerMeshReindex.measurable (measurable_pathHeatWienerMeshSample c)]
  rfl

theorem pathHeatWienerMeshReindexedLaw_centered
    (c : Fin j → Fin (n+1) → Paper.Overlap) :
    (∫ x, x ∂pathHeatWienerMeshReindexedLaw c) = 0 := by
  rw [pathHeatWienerMeshReindexedLaw,integral_map (by fun_prop) (by fun_prop)]
  change (∫ x, pathHeatWienerMeshReindex x ∂pathHeatWienerMeshLaw c) = 0
  rw [pathHeatWienerMeshReindex.integral_comp_id_comm IsGaussian.integrable_id,
    pathHeatWienerMesh_centered,map_zero]

theorem pathHeatWienerMeshReindexedLaw_covariance
    (c : Fin j → Fin (n+1) → Paper.Overlap) (p q : Fin (j*(n+1))) :
    covarianceBilin (pathHeatWienerMeshReindexedLaw c)
      (EuclideanSpace.single p 1) (EuclideanSpace.single q 1) =
      if (finProdFinEquiv.symm p).1=(finProdFinEquiv.symm q).1 then
        min (c (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 : ℝ)
          (c (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 : ℝ) else 0 := by
  rw [covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
  simp only [EuclideanSpace.inner_single_left,starRingEnd_apply,star_trivial,one_mul]
  rw [pathHeatWienerMeshReindexedLaw,covariance_map_fun (by fun_prop) (by fun_prop)
    pathHeatWienerMeshReindex.measurable.aemeasurable]
  simp only [pathHeatWienerMeshReindex_apply]
  have h := pathHeatWienerMesh_covariance c
    (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1
    (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2
  rw [covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id] at h
  simpa only [EuclideanSpace.inner_single_left,starRingEnd_apply,star_trivial,one_mul] using h

end HexagonPaper
