module
public import HexagonPaper.PathHeatTreeBernsteinFlatten
public import HexagonPaper.PathHeatTreeBernsteinReconstructionMixedCovariance

@[expose] public section

/-! Physical mixed tree/finite-coordinate synthesis in the actual flattened
Wiener clock coordinates, and its exact signed covariance contraction. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def pathHeatTreeMixedFlattenedSynthesis (n L : ℕ)
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) :
    QuantitativePaper.Field (L*(n+1)) →L[ℝ] C(Fin L × I,ℝ) :=
  (pathHeatTreeMixedOperator δ W).comp (pathHeatTreeBernsteinFlattenedSynthesis n L)

theorem pathHeatTreeMixedFlattenedSynthesis_basis (n L : ℕ)
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) (p : Fin (L*(n+1))) :
    pathHeatTreeMixedFlattenedSynthesis n L δ W (EuclideanSpace.single p 1) =
      pathHeatTreeMixedOperator δ W
        (pathHeatTreeBernsteinBasis n L (finProdFinEquiv.symm p)) := by
  change pathHeatTreeMixedOperator δ W
    (pathHeatTreeBernsteinFlattenedSynthesis n L (EuclideanSpace.single p 1)) = _
  rw [pathHeatTreeBernsteinFlattenedSynthesis_basis]

theorem pathHeatTreeMixedFlattenedSynthesis_actualReindex (n L : ℕ)
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ)
    (g : EuclideanSpace ℝ (Fin L × Fin (n+1))) :
    pathHeatTreeMixedFlattenedSynthesis n L δ W (pathHeatWienerMeshReindex g) =
      pathHeatTreeMixedOperator δ W (pathHeatTreeBernsteinSynthesis n L g) := by
  change pathHeatTreeMixedOperator δ W
    (pathHeatTreeBernsteinFlattenedSynthesis n L (pathHeatWienerMeshReindex g)) = _
  rw [pathHeatTreeBernsteinFlattenedSynthesis_actualReindex]

theorem norm_pathHeatTreeMixedFlattenedSynthesis_le (n L : ℕ)
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ) :
    ‖pathHeatTreeMixedFlattenedSynthesis n L δ W‖ ≤ pathHeatTreeMixedBound δ W := by
  apply ContinuousLinearMap.opNorm_le_bound _ (pathHeatTreeMixedBound_nonneg δ W)
  intro g
  change ‖pathHeatTreeMixedOperator δ W (pathHeatTreeBernsteinFlattenedSynthesis n L g)‖ ≤ _
  calc
    _ ≤ pathHeatTreeMixedBound δ W * ‖pathHeatTreeBernsteinFlattenedSynthesis n L g‖ :=
      pathHeatTreeMixedOperator_norm_apply_le δ W _
    _ ≤ pathHeatTreeMixedBound δ W * ‖g‖ := by
      apply mul_le_mul_of_nonneg_left _ (pathHeatTreeMixedBound_nonneg δ W)
      exact ((pathHeatTreeBernsteinFlattenedSynthesis n L).le_opNorm g).trans
        (by
          simpa using mul_le_mul_of_nonneg_right
            (norm_pathHeatTreeBernsteinFlattenedSynthesis_le n L) (norm_nonneg g))

theorem pathHeatTreeMixedFlattened_signed_covariance_contraction (n L : ℕ)
    (δ : Fin L → ℝ) (W : Fin L → Fin L → ℝ)
    (K : C(Fin L × I,C(Fin L × I,ℝ)))
    (M : SignedMeasure ((Fin L × I) × (Fin L × I))) :
    (∑p : Fin (L*(n+1)), ∑q : Fin (L*(n+1)),
      K ((finProdFinEquiv.symm p).1,bernstein.z (finProdFinEquiv.symm p).2)
        ((finProdFinEquiv.symm q).1,bernstein.z (finProdFinEquiv.symm q).2) *
        pathHeatSignedHessian M
          (pathHeatTreeMixedFlattenedSynthesis n L δ W (EuclideanSpace.single p 1))
          (pathHeatTreeMixedFlattenedSynthesis n L δ W (EuclideanSpace.single q 1))) =
      signedContraction (BoundedContinuousFunction.mkOfCompact
        (pathHeatTreeMixedKernelOperator δ W (pathHeatTreeKernelSample n L K)).uncurry) M := by
  rw [←finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  simp_rw [←finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply,pathHeatTreeMixedFlattenedSynthesis_basis]
  simpa only [pathHeatTreeBernsteinSynthesis_basis] using
    pathHeatTreeMixedBernstein_signed_covariance_contraction n L δ W K M

end HexagonPaper
