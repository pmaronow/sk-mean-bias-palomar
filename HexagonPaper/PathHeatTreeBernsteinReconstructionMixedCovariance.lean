module
public import HexagonPaper.PathHeatTreeBernsteinReconstructionMixed

@[expose] public section

/-! The literal covariance and signed Hessian contraction for physical tree
edges together with finite coordinates embedded as constant terminal rows. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pathHeatTreeMixedOperator_norm_apply_le {L : ℕ}
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) (f : C(Fin L × I,E)) :
    ‖pathHeatTreeMixedOperator δ W f‖ ≤ pathHeatTreeMixedBound δ W * ‖f‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (pathHeatTreeMixedBound_nonneg δ W) (norm_nonneg f))).mpr
  intro x
  change ‖(δ x.1-1) • f x + pathHeatTreeAncestorReconstruct W f x‖ ≤ _
  calc
    _ ≤ ‖(δ x.1-1) • f x‖ + ‖pathHeatTreeAncestorReconstruct W f x‖ := norm_add_le _ _
    _ ≤ ‖pathHeatTreeDiagonalColumn (fun l => δ l-1)‖ * ‖f‖ +
        pathHeatTreeAncestorBound W * ‖f‖ := by
      apply add_le_add
      · rw [norm_smul]
        exact mul_le_mul ((pathHeatTreeDiagonalColumn (fun l => δ l-1)).norm_coe_le_norm x)
          (f.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)
      · exact ((pathHeatTreeAncestorReconstruct W f).norm_coe_le_norm x).trans
          (norm_pathHeatTreeAncestorReconstruct_le W f)
    _ = pathHeatTreeMixedBound δ W * ‖f‖ := by rw [pathHeatTreeMixedBound,add_mul]

def pathHeatTreeMixedKernelOperator {L : ℕ} (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) :
    C(Fin L × I,C(Fin L × I,E)) →L[ℝ] C(Fin L × I,C(Fin L × I,E)) :=
  (pathHeatTreeMixedOperator δ W).comp ((pathHeatTreeKernelTransposeCLM L).comp
    ((pathHeatTreeMixedOperator δ W).comp (pathHeatTreeKernelTransposeCLM L)))

theorem pathHeatTreeMixedKernelOperator_apply {L : ℕ}
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ)
    (K : C(Fin L × I,C(Fin L × I,E))) (x y : Fin L × I) :
    pathHeatTreeMixedKernelOperator δ W K x y =
      δ x.1 • (δ y.1 • K x y + ∑b : Fin L, W y.1 b • K x (b,1)) +
        ∑a : Fin L, W x.1 a •
          (δ y.1 • K (a,1) y + ∑b : Fin L, W y.1 b • K (a,1) (b,1)) := by
  change pathHeatTreeMixedOperator δ W (pathHeatTreeKernelTranspose
    (pathHeatTreeMixedOperator δ W (pathHeatTreeKernelTranspose K))) x y = _
  simp only [pathHeatTreeMixedOperator_apply,pathHeatTreeKernelTranspose_apply,
    ContinuousMap.add_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply]

theorem pathHeatTreeMixedKernelOperator_four_terms {L : ℕ}
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ)
    (K : C(Fin L × I,C(Fin L × I,E))) (x y : Fin L × I) :
    pathHeatTreeMixedKernelOperator δ W K x y =
      (δ x.1 * δ y.1) • K x y +
        (∑b : Fin L, (δ x.1 * W y.1 b) • K x (b,1)) +
        (∑a : Fin L, (W x.1 a * δ y.1) • K (a,1) y) +
        ∑a : Fin L, ∑b : Fin L, (W x.1 a * W y.1 b) • K (a,1) (b,1) := by
  rw [pathHeatTreeMixedKernelOperator_apply]
  simp only [smul_add,Finset.smul_sum,smul_smul,Finset.sum_add_distrib]
  abel

theorem norm_pathHeatTreeMixedKernelOperator_apply_le {L : ℕ}
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ)
    (K : C(Fin L × I,C(Fin L × I,E))) :
    ‖pathHeatTreeMixedKernelOperator δ W K‖ ≤ (pathHeatTreeMixedBound δ W)^2 * ‖K‖ := by
  let B := pathHeatTreeMixedBound δ W
  have hB : 0 ≤ B := pathHeatTreeMixedBound_nonneg δ W
  have hr : ‖pathHeatTreeKernelTranspose
      (pathHeatTreeMixedOperator δ W (pathHeatTreeKernelTranspose K))‖ ≤ B*‖K‖ := by
    exact (norm_pathHeatTreeKernelTranspose_le _).trans ((pathHeatTreeMixedOperator_norm_apply_le δ W _).trans
      (mul_le_mul_of_nonneg_left (norm_pathHeatTreeKernelTranspose_le K) hB))
  change ‖pathHeatTreeMixedOperator δ W (pathHeatTreeKernelTranspose
    (pathHeatTreeMixedOperator δ W (pathHeatTreeKernelTranspose K)))‖ ≤ B^2*‖K‖
  exact (pathHeatTreeMixedOperator_norm_apply_le δ W _).trans
    (by simpa only [pow_two,mul_assoc] using mul_le_mul_of_nonneg_left hr hB)

theorem tendsto_pathHeatTreeMixedKernelSample {L : ℕ}
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ)
    (K : C(Fin L × I,C(Fin L × I,E))) :
    Tendsto (fun n => pathHeatTreeMixedKernelOperator δ W (pathHeatTreeKernelSample n L K))
      atTop (𝓝 (pathHeatTreeMixedKernelOperator δ W K)) :=
  (pathHeatTreeMixedKernelOperator δ W).continuous.continuousAt.tendsto.comp
    (tendsto_pathHeatTreeKernelSample L K)

theorem pathHeatTreeMixedKernelOperator_tensor {L : ℕ}
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) (h k : C(Fin L × I,ℝ)) :
    pathHeatTreeMixedKernelOperator δ W (pathHeatTensor h k).curry =
      (pathHeatTensor (pathHeatTreeMixedOperator δ W h)
        (pathHeatTreeMixedOperator δ W k)).curry := by
  ext x y
  let F := pathHeatTreeKernelTranspose
    (pathHeatTreeMixedOperator δ W (pathHeatTreeKernelTranspose (pathHeatTensor h k).curry))
  have hr (u v : Fin L × I) : F u v = h u * pathHeatTreeMixedOperator δ W k v := by
    change pathHeatTreeMixedOperator δ W
      (pathHeatTreeKernelTranspose (pathHeatTensor h k).curry) v u = _
    simp only [pathHeatTreeMixedOperator_apply,ContinuousMap.add_apply,
      ContinuousMap.sum_apply,ContinuousMap.smul_apply,pathHeatTreeKernelTranspose_apply,
      pathHeatTensor,ContinuousMap.curry_apply,ContinuousMap.coe_mk,smul_eq_mul]
    rw [mul_add,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro b _; ring
  change pathHeatTreeMixedOperator δ W F x y =
    pathHeatTreeMixedOperator δ W h x * pathHeatTreeMixedOperator δ W k y
  simp only [pathHeatTreeMixedOperator_apply,ContinuousMap.add_apply,
    ContinuousMap.sum_apply,ContinuousMap.smul_apply,hr,smul_eq_mul]
  rw [add_mul,Finset.sum_mul]
  congr 1
  · ring
  · apply Finset.sum_congr rfl; intro a _; ring

theorem pathHeatTreeMixedKernelSample_uncurry_sum (n L : ℕ)
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ)
    (K : C(Fin L × I,C(Fin L × I,ℝ))) :
    (pathHeatTreeMixedKernelOperator δ W (pathHeatTreeKernelSample n L K)).uncurry =
      ∑p : Fin L × Fin (n+1), ∑q : Fin L × Fin (n+1),
        K (p.1,bernstein.z p.2) (q.1,bernstein.z q.2) •
          pathHeatTensor
            (pathHeatTreeMixedOperator δ W (pathHeatTreeBernsteinBasis n L p))
            (pathHeatTreeMixedOperator δ W (pathHeatTreeBernsteinBasis n L q)) := by
  have he : pathHeatTreeKernelSample n L K =
      ∑p : Fin L × Fin (n+1), ∑q : Fin L × Fin (n+1),
        K (p.1,bernstein.z p.2) (q.1,bernstein.z q.2) •
          (pathHeatTensor (pathHeatTreeBernsteinBasis n L p)
            (pathHeatTreeBernsteinBasis n L q)).curry := by
    ext x y
    have hh := congrArg (fun F : C((Fin L × I) × (Fin L × I),ℝ) => F (x,y))
      (pathHeatTreeKernelSample_uncurry_sum n L K)
    simpa only [ContinuousMap.uncurry_apply,Function.uncurry_apply_pair,
      ContinuousMap.curry_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply] using hh
  rw [he,map_sum]
  simp only [map_sum,map_smul,pathHeatTreeMixedKernelOperator_tensor]
  ext x
  rcases x with ⟨x,y⟩
  simp only [ContinuousMap.uncurry_apply,Function.uncurry_apply_pair,
    ContinuousMap.curry_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply]

theorem pathHeatTreeMixedBernstein_signed_covariance_contraction (n L : ℕ)
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ)
    (K : C(Fin L × I,C(Fin L × I,ℝ)))
    (M : SignedMeasure ((Fin L × I) × (Fin L × I))) :
    (∑p : Fin L × Fin (n+1), ∑q : Fin L × Fin (n+1),
      K (p.1,bernstein.z p.2) (q.1,bernstein.z q.2) *
        pathHeatSignedHessian M
          (pathHeatTreeMixedOperator δ W
            (pathHeatTreeBernsteinSynthesis n L (EuclideanSpace.single p 1)))
          (pathHeatTreeMixedOperator δ W
            (pathHeatTreeBernsteinSynthesis n L (EuclideanSpace.single q 1)))) =
      signedContraction (BoundedContinuousFunction.mkOfCompact
        (pathHeatTreeMixedKernelOperator δ W (pathHeatTreeKernelSample n L K)).uncurry) M := by
  change _ = pathHeatSignedScore M
    (pathHeatTreeMixedKernelOperator δ W (pathHeatTreeKernelSample n L K)).uncurry
  rw [pathHeatTreeMixedKernelSample_uncurry_sum,map_sum]
  simp only [map_sum,map_smul,smul_eq_mul,pathHeatTreeBernsteinSynthesis_basis]
  rfl

end HexagonPaper
