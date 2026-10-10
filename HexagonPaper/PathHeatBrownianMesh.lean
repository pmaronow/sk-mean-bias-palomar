module
public import HexagonPaper.PathHeatBrownianMeshBasic

@[expose] public section

/-! Independent finite meshes of actual canonical continuous Wiener paths.
The joint Gaussian law, its center and its covariance are derived from the
actual product measure; arbitrary clocks may repeat or be unordered. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal ENNReal BigOperators
namespace HexagonPaper
open Paper FourPapersCommon QuantitativePaper
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {J : Type*} [Fintype J] [DecidableEq J] {M : ℕ}

abbrev pathHeatWienerMeshField (J : Type*) (M : ℕ) := EuclideanSpace ℝ (J × Fin M)

def pathHeatWienerMeshBase : Measure (J → WienerPath) :=
  Measure.pi (fun _ : J => canonicalWienerMeasure)

instance pathHeatWienerMeshBase_probability : IsProbabilityMeasure
    (pathHeatWienerMeshBase (J:=J)) := by
  unfold pathHeatWienerMeshBase
  infer_instance

def pathHeatWienerMeshFlatten : (J → Field M) →L[ℝ] pathHeatWienerMeshField J M :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : J × Fin M => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun p : J × Fin M =>
      (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin M => ℝ) p.2).comp
        (ContinuousLinearMap.proj p.1))

def pathHeatWienerMeshSample (c : J → Fin M → Paper.Overlap)
    (w : J → WienerPath) : pathHeatWienerMeshField J M :=
  pathHeatWienerMeshFlatten (fun j => pathHeatWienerClockSample (c j) (w j))

@[simp] theorem pathHeatWienerMeshSample_apply (c : J → Fin M → Paper.Overlap)
    (w : J → WienerPath) (j : J) (i : Fin M) :
    pathHeatWienerMeshSample c w (j,i) = w j (c j i) := rfl

theorem measurable_pathHeatWienerMeshSample (c : J → Fin M → Paper.Overlap) :
    Measurable (pathHeatWienerMeshSample c) := by
  unfold pathHeatWienerMeshSample
  exact (pathHeatWienerMeshFlatten (J:=J) (M:=M)).measurable.comp (Measurable.of_eval
    (fun j => (measurable_pathHeatWienerClockSample (c j)).comp (measurable_pi_apply j)))

def pathHeatWienerMeshLaw (c : J → Fin M → Paper.Overlap) :
    Measure (pathHeatWienerMeshField J M) :=
  (pathHeatWienerMeshBase (J:=J)).map (pathHeatWienerMeshSample c)

theorem pathHeatWienerMesh_hasGaussianLaw (c : J → Fin M → Paper.Overlap) :
    HasGaussianLaw (pathHeatWienerMeshSample c) (pathHeatWienerMeshBase (J:=J)) := by
  have hG (j : J) : HasGaussianLaw
      (fun w : J → WienerPath => pathHeatWienerClockSample (c j) (w j))
      (pathHeatWienerMeshBase (J:=J)) := by
    let ν := canonicalWienerMeasure.map (pathHeatWienerClockSample (c j))
    haveI : IsGaussian ν := (pathHeatWienerClock_hasGaussianLaw (c j)).isGaussian_map
    have hS : HasLaw (pathHeatWienerClockSample (c j)) ν canonicalWienerMeasure :=
      ⟨(measurable_pathHeatWienerClockSample (c j)).aemeasurable,rfl⟩
    exact (hS.comp (measurePreserving_eval
      (fun _ : J => canonicalWienerMeasure) j).hasLaw).hasGaussianLaw
  have hInd := iIndepFun_pi (μ:=fun _ : J => canonicalWienerMeasure)
    (X:=fun j => pathHeatWienerClockSample (c j))
    (fun j => (measurable_pathHeatWienerClockSample (c j)).aemeasurable)
  exact (hInd.hasGaussianLaw hG).map_fun pathHeatWienerMeshFlatten

instance pathHeatWienerMesh_isGaussian (c : J → Fin M → Paper.Overlap) :
    IsGaussian (pathHeatWienerMeshLaw c) :=
  (pathHeatWienerMesh_hasGaussianLaw c).isGaussian_map

theorem hasLaw_pathHeatWienerMesh_coordinate (c : J → Fin M → Paper.Overlap)
    (j : J) (i : Fin M) :
    HasLaw (fun w => pathHeatWienerMeshSample c w (j,i))
      (gaussianReal 0 (c j i).1.toNNReal) (pathHeatWienerMeshBase (J:=J)) :=
  (hasLaw_pathHeatWiener_eval (c j i)).comp
    (measurePreserving_eval (fun _ : J => canonicalWienerMeasure) j).hasLaw

theorem pathHeatWienerMesh_centered (c : J → Fin M → Paper.Overlap) :
    (∫ x, x ∂pathHeatWienerMeshLaw c) = 0 := by
  ext p
  have hc : (∫ x, x ∂pathHeatWienerMeshLaw c) p =
      ∫ x, x p ∂pathHeatWienerMeshLaw c := by
    have h := (PiLp.proj (𝕜:=ℝ) 2 (fun _ : J × Fin M => ℝ) p).integral_comp_id_comm (IsGaussian.integrable_id (μ:=pathHeatWienerMeshLaw c))
    simpa only [PiLp.proj_apply,id_eq] using h.symm
  rw [hc,pathHeatWienerMeshLaw,integral_map
    (measurable_pathHeatWienerMeshSample c).aemeasurable (by fun_prop)]
  change (∫ w, pathHeatWienerMeshSample c w (p.1,p.2)
    ∂pathHeatWienerMeshBase (J:=J)) = 0
  rw [(hasLaw_pathHeatWienerMesh_coordinate c p.1 p.2).integral_eq,
    integral_id_gaussianReal]

theorem pathHeatWienerMesh_covariance (c : J → Fin M → Paper.Overlap)
    (j k : J) (i l : Fin M) :
    covarianceBilin (pathHeatWienerMeshLaw c)
      (EuclideanSpace.single (j,i) 1) (EuclideanSpace.single (k,l) 1) =
      if j=k then min (c j i : ℝ) (c k l : ℝ) else 0 := by
  rw [covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
  simp only [EuclideanSpace.inner_single_left,starRingEnd_apply,star_trivial,one_mul]
  rw [pathHeatWienerMeshLaw,covariance_map_fun (by fun_prop) (by fun_prop)
    (measurable_pathHeatWienerMeshSample c).aemeasurable]
  simp only [pathHeatWienerMeshSample_apply]
  by_cases hjk : j=k
  · subst k
    rw [if_pos rfl]
    have h := (measurePreserving_eval (fun _ : J => canonicalWienerMeasure) j).hasLaw.covariance_fun_comp (f:=fun p : WienerPath => p (c j i))
        (g:=fun p : WienerPath => p (c j l))
        (_root_.ContinuousMap.measurable_eval (c j i)).aemeasurable
        (_root_.ContinuousMap.measurable_eval (c j l)).aemeasurable
    exact h.trans (covariance_pathHeatWiener_eval (c j i) (c j l))
  · rw [if_neg hjk]
    have hPaths := iIndepFun_pi (μ:=fun _ : J => canonicalWienerMeasure)
      (X:=fun _ : J => id) (fun _ => aemeasurable_id)
    have hInd := (hPaths.indepFun hjk).comp
      (_root_.ContinuousMap.measurable_eval (c j i))
      (_root_.ContinuousMap.measurable_eval (c k l))
    exact hInd.covariance_eq_zero
      (hasLaw_pathHeatWienerMesh_coordinate c j i).hasGaussianLaw.memLp_two
      (hasLaw_pathHeatWienerMesh_coordinate c k l).hasGaussianLaw.memLp_two

end HexagonPaper
