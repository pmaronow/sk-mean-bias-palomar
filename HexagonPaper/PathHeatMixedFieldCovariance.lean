module
public import HexagonPaper.PathHeatClockKernelCovariance
public import HexagonPaper.PathHeatFlatClockCoupling

@[expose] public section

/-! The continuous mixed tree kernel is the covariance of actual physical
Wiener field evaluations at arbitrary levels, not only mesh points. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped unitInterval Topology BigOperators
namespace HexagonPaper
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {L : ℕ}

theorem hasLaw_pathHeatFlatClockEvaluation (c : Fin L→C(I,I)) (x : Fin L×I) :
    HasLaw (fun w => pathHeatFlatClockPath L c w x)
      (gaussianReal 0 (c x.1 x.2).1.toNNReal) (pathHeatWienerMeshBase (J:=Fin L)) := by
  simpa only [pathHeatFlatClockPath_apply,pathHeatWienerMeshSample_apply] using
    hasLaw_pathHeatWienerMesh_coordinate (fun l (_ : Fin 1) => c l x.2) x.1 0

theorem memLp_pathHeatFlatClockEvaluation (c : Fin L→C(I,I)) (x : Fin L×I) :
    MemLp (fun w => pathHeatFlatClockPath L c w x) 2
      (pathHeatWienerMeshBase (J:=Fin L)) :=
  (hasLaw_pathHeatFlatClockEvaluation c x).hasGaussianLaw.memLp_two

theorem integral_pathHeatFlatClockEvaluation (c : Fin L→C(I,I)) (x : Fin L×I) :
    (∫w,pathHeatFlatClockPath L c w x ∂pathHeatWienerMeshBase (J:=Fin L))=0 := by
  rw [(hasLaw_pathHeatFlatClockEvaluation c x).integral_eq,integral_id_gaussianReal]

theorem covariance_pathHeatFlatClockEvaluation (c : Fin L→C(I,I))
    (hc : ∀l,Monotone (c l)) (x y : Fin L×I) :
    covariance (fun w => pathHeatFlatClockPath L c w x)
      (fun w => pathHeatFlatClockPath L c w y) (pathHeatWienerMeshBase (J:=Fin L)) =
        pathHeatClockRawKernel (pathHeatClockReal c) x y := by
  let times : Fin L→Fin 2→Paper.Overlap := fun l i => if i=0 then c l x.2 else c l y.2
  have h := pathHeatWienerMesh_covariance times x.1 y.1 (0:Fin 2) (1:Fin 2)
  rw [covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id] at h
  simp only [EuclideanSpace.inner_single_left,starRingEnd_apply,star_trivial,one_mul] at h
  rw [pathHeatWienerMeshLaw,covariance_map_fun (by fun_prop) (by fun_prop)
    (measurable_pathHeatWienerMeshSample times).aemeasurable] at h
  simp only [pathHeatWienerMeshSample_apply,times,ite_true,
    show (1:Fin 2)≠0 by decide,ite_false] at h
  simp only [pathHeatFlatClockPath_apply,pathHeatClockRawKernel_apply,pathHeatClockReal_apply]
  rw [h]
  by_cases hxy : x.1=y.1
  · simp only [hxy,ite_true]
    exact pathHeatClock_min_covariance c hc _ _ _
  · simp only [hxy,ite_false]

def pathHeatMixedEvaluationIndex (x : Fin L×I) : Option (Fin L)→Fin L×I
  | none => x
  | some a => (a,1)

def pathHeatMixedEvaluationWeight (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (x : Fin L×I) : Option (Fin L)→ℝ
  | none => δ x.1
  | some a => W x.1 a

theorem pathHeatMixedEvaluation_sum (c : Fin L→C(I,I))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (w : Fin L→WienerPath) (x : Fin L×I) :
    pathHeatTreeMixedOperator δ W (pathHeatFlatClockPath L c w) x =
      ∑i : Option (Fin L),pathHeatMixedEvaluationWeight δ W x i *
        pathHeatFlatClockPath L c w (pathHeatMixedEvaluationIndex x i) := by
  rw [Fintype.sum_option,pathHeatTreeMixedOperator_apply]
  simp only [pathHeatMixedEvaluationWeight,pathHeatMixedEvaluationIndex,smul_eq_mul]

theorem covariance_pathHeatMixedClockEvaluation (c : Fin L→C(I,I))
    (hc : ∀l,Monotone (c l)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (x y : Fin L×I) :
    covariance (fun w => pathHeatTreeMixedOperator δ W (pathHeatFlatClockPath L c w) x)
      (fun w => pathHeatTreeMixedOperator δ W (pathHeatFlatClockPath L c w) y)
        (pathHeatWienerMeshBase (J:=Fin L)) =
      pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel (pathHeatClockReal c)) x y := by
  simp_rw [pathHeatMixedEvaluation_sum]
  rw [covariance_fun_sum_fun_sum
    (fun i => (memLp_pathHeatFlatClockEvaluation c (pathHeatMixedEvaluationIndex x i)).const_mul _)
    (fun i => (memLp_pathHeatFlatClockEvaluation c (pathHeatMixedEvaluationIndex y i)).const_mul _)]
  simp_rw [covariance_const_mul_left,covariance_const_mul_right,
    covariance_pathHeatFlatClockEvaluation c hc]
  rw [Fintype.sum_option]
  simp_rw [Fintype.sum_option]
  simp only [pathHeatMixedEvaluationWeight,pathHeatMixedEvaluationIndex,
    pathHeatTreeMixedKernelOperator_four_terms,smul_eq_mul]
  rw [Finset.sum_add_distrib]
  simp_rw [←mul_assoc]
  ring

end HexagonPaper
