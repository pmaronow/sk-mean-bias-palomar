module
public import HexagonPaper.PathHeatTreeBernsteinReconstruction
public import HexagonPaper.PathHeatTreeBernsteinContraction

@[expose] public section

/-! Covariance reconstruction under the literal ancestor terminal map, in
both slots. This retains cross-edge covariances and all terminal charges. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pathHeatTreeAncestorKernelOperator {L : ℕ} (W : Fin L → Fin L → ℝ) :
    C(Fin L × I,C(Fin L × I,E)) →L[ℝ] C(Fin L × I,C(Fin L × I,E)) :=
  (pathHeatTreeAncestorOperator W).comp
    ((pathHeatTreeKernelTransposeCLM L).comp
      ((pathHeatTreeAncestorOperator W).comp (pathHeatTreeKernelTransposeCLM L)))

theorem pathHeatTreeAncestorKernelOperator_apply {L : ℕ}
    (W : Fin L → Fin L → ℝ) (K : C(Fin L × I,C(Fin L × I,E))) (x y : Fin L × I) :
    pathHeatTreeAncestorKernelOperator W K x y =
      K x y + ∑b : Fin L, W y.1 b • K x (b,1) +
        ∑a : Fin L, W x.1 a •
          (K (a,1) y + ∑b : Fin L, W y.1 b • K (a,1) (b,1)) := by
  change pathHeatTreeAncestorReconstruct W (pathHeatTreeKernelTranspose
    (pathHeatTreeAncestorReconstruct W (pathHeatTreeKernelTranspose K))) x y = _
  simp only [pathHeatTreeAncestorReconstruct_apply,pathHeatTreeKernelTranspose_apply,
    ContinuousMap.add_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply]

theorem pathHeatTreeAncestorKernelOperator_four_terms {L : ℕ}
    (W : Fin L → Fin L → ℝ) (K : C(Fin L × I,C(Fin L × I,E))) (x y : Fin L × I) :
    pathHeatTreeAncestorKernelOperator W K x y =
      K x y + (∑b : Fin L, W y.1 b • K x (b,1)) +
        (∑a : Fin L, W x.1 a • K (a,1) y) +
        ∑a : Fin L, ∑b : Fin L, (W x.1 a * W y.1 b) • K (a,1) (b,1) := by
  rw [pathHeatTreeAncestorKernelOperator_apply]
  simp only [smul_add,Finset.smul_sum,smul_smul,Finset.sum_add_distrib]
  abel

theorem norm_pathHeatTreeAncestorKernelOperator_apply_le {L : ℕ}
    (W : Fin L → Fin L → ℝ) (K : C(Fin L × I,C(Fin L × I,E))) :
    ‖pathHeatTreeAncestorKernelOperator W K‖ ≤ (pathHeatTreeAncestorBound W)^2 * ‖K‖ := by
  let B := pathHeatTreeAncestorBound W
  have hB : 0 ≤ B := pathHeatTreeAncestorBound_nonneg W
  have hr : ‖pathHeatTreeKernelTranspose
      (pathHeatTreeAncestorOperator W (pathHeatTreeKernelTranspose K))‖ ≤ B*‖K‖ := by
    exact (norm_pathHeatTreeKernelTranspose_le _).trans
      ((norm_pathHeatTreeAncestorReconstruct_le W _).trans
        (mul_le_mul_of_nonneg_left (norm_pathHeatTreeKernelTranspose_le K) hB))
  change ‖pathHeatTreeAncestorOperator W (pathHeatTreeKernelTranspose
    (pathHeatTreeAncestorOperator W (pathHeatTreeKernelTranspose K)))‖ ≤ B^2*‖K‖
  exact (norm_pathHeatTreeAncestorReconstruct_le W _).trans
    (by simpa only [pow_two,mul_assoc] using mul_le_mul_of_nonneg_left hr hB)

theorem tendsto_pathHeatTreeAncestorKernelSample {L : ℕ}
    (W : Fin L → Fin L → ℝ) (K : C(Fin L × I,C(Fin L × I,E))) :
    Tendsto (fun n => pathHeatTreeAncestorKernelOperator W (pathHeatTreeKernelSample n L K))
      atTop (𝓝 (pathHeatTreeAncestorKernelOperator W K)) :=
  (pathHeatTreeAncestorKernelOperator W).continuous.continuousAt.tendsto.comp
    (tendsto_pathHeatTreeKernelSample L K)

theorem pathHeatTreeAncestorKernelOperator_tensor {L : ℕ}
    (W : Fin L → Fin L → ℝ) (h k : C(Fin L × I,ℝ)) :
    pathHeatTreeAncestorKernelOperator W (pathHeatTensor h k).curry =
      (pathHeatTensor (pathHeatTreeAncestorOperator W h)
        (pathHeatTreeAncestorOperator W k)).curry := by
  ext x y
  let F := pathHeatTreeKernelTranspose
    (pathHeatTreeAncestorOperator W (pathHeatTreeKernelTranspose (pathHeatTensor h k).curry))
  have hr (u v : Fin L × I) : F u v = h u * pathHeatTreeAncestorOperator W k v := by
    change pathHeatTreeAncestorReconstruct W
      (pathHeatTreeKernelTranspose (pathHeatTensor h k).curry) v u = _
    simp only [pathHeatTreeAncestorReconstruct_apply,ContinuousMap.add_apply,
      ContinuousMap.sum_apply,ContinuousMap.smul_apply,pathHeatTreeKernelTranspose_apply,
      pathHeatTensor,ContinuousMap.curry_apply,ContinuousMap.coe_mk,
      pathHeatTreeAncestorOperator_apply,smul_eq_mul]
    rw [mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro b _; ring
  change pathHeatTreeAncestorReconstruct W F x y =
    pathHeatTreeAncestorOperator W h x * pathHeatTreeAncestorOperator W k y
  simp only [pathHeatTreeAncestorReconstruct_apply,ContinuousMap.add_apply,
    ContinuousMap.sum_apply,ContinuousMap.smul_apply,hr,smul_eq_mul]
  change h x * pathHeatTreeAncestorOperator W k y +
    ∑a : Fin L, W x.1 a * (h (a,1) * pathHeatTreeAncestorOperator W k y) =
      (h x + ∑a : Fin L, W x.1 a * h (a,1)) * pathHeatTreeAncestorOperator W k y
  rw [add_mul,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl; intro a _; ring

theorem pathHeatTreeAncestorKernelSample_uncurry_sum (n L : ℕ)
    (W : Fin L → Fin L → ℝ) (K : C(Fin L × I,C(Fin L × I,ℝ))) :
    (pathHeatTreeAncestorKernelOperator W (pathHeatTreeKernelSample n L K)).uncurry =
      ∑p : Fin L × Fin (n+1), ∑q : Fin L × Fin (n+1),
        K (p.1,bernstein.z p.2) (q.1,bernstein.z q.2) •
          pathHeatTensor
            (pathHeatTreeAncestorOperator W (pathHeatTreeBernsteinBasis n L p))
            (pathHeatTreeAncestorOperator W (pathHeatTreeBernsteinBasis n L q)) := by
  have he : pathHeatTreeKernelSample n L K =
      ∑p : Fin L × Fin (n+1), ∑q : Fin L × Fin (n+1),
        K (p.1,bernstein.z p.2) (q.1,bernstein.z q.2) •
          (pathHeatTensor (pathHeatTreeBernsteinBasis n L p)
            (pathHeatTreeBernsteinBasis n L q)).curry := by
    ext x y
    have hh := congrArg (fun F : C((Fin L × I) × (Fin L × I),ℝ) => F (x,y))
      (pathHeatTreeKernelSample_uncurry_sum n L K)
    simpa only [ContinuousMap.uncurry_apply,Function.uncurry_apply_pair,ContinuousMap.curry_apply,
      ContinuousMap.sum_apply,ContinuousMap.smul_apply] using hh
  rw [he,map_sum]
  simp only [map_sum,map_smul,pathHeatTreeAncestorKernelOperator_tensor]
  ext x
  rcases x with ⟨x,y⟩
  simp only [ContinuousMap.uncurry_apply,Function.uncurry_apply_pair,ContinuousMap.curry_apply,
    ContinuousMap.sum_apply,ContinuousMap.smul_apply]

theorem pathHeatTreeAncestorBernstein_signed_covariance_contraction (n L : ℕ)
    (W : Fin L → Fin L → ℝ) (K : C(Fin L × I,C(Fin L × I,ℝ)))
    (M : SignedMeasure ((Fin L × I) × (Fin L × I))) :
    (∑p : Fin L × Fin (n+1), ∑q : Fin L × Fin (n+1),
      K (p.1,bernstein.z p.2) (q.1,bernstein.z q.2) *
        pathHeatSignedHessian M
          (pathHeatTreeAncestorOperator W
            (pathHeatTreeBernsteinSynthesis n L (EuclideanSpace.single p 1)))
          (pathHeatTreeAncestorOperator W
            (pathHeatTreeBernsteinSynthesis n L (EuclideanSpace.single q 1)))) =
      signedContraction (BoundedContinuousFunction.mkOfCompact
        (pathHeatTreeAncestorKernelOperator W (pathHeatTreeKernelSample n L K)).uncurry) M := by
  change _ = pathHeatSignedScore M
    (pathHeatTreeAncestorKernelOperator W (pathHeatTreeKernelSample n L K)).uncurry
  rw [pathHeatTreeAncestorKernelSample_uncurry_sum,map_sum]
  simp only [map_sum,map_smul,smul_eq_mul,pathHeatTreeBernsteinSynthesis_basis]
  rfl

end HexagonPaper
