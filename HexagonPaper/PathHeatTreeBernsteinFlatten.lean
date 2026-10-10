module
public import HexagonPaper.PathHeatTreeBernsteinContraction
public import HexagonPaper.PathHeatBrownianClockReindex

@[expose] public section

/-! The same actual synthesis in the canonical `Fin (L*(n+1))` coordinates
used by the Gaussian clock factor. Reindexing is a genuine linear isometry. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def pathHeatTreeBernsteinUnflatten (n L : ℕ) :
    QuantitativePaper.Field (L*(n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin L × Fin (n+1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finProdFinEquiv.symm

@[simp] theorem pathHeatTreeBernsteinUnflatten_apply (n L : ℕ)
    (g : QuantitativePaper.Field (L*(n+1))) (p : Fin L × Fin (n+1)) :
    pathHeatTreeBernsteinUnflatten n L g p = g (finProdFinEquiv p) := rfl

theorem pathHeatTreeBernsteinUnflatten_actualReindex (n L : ℕ)
    (g : EuclideanSpace ℝ (Fin L × Fin (n+1))) :
    pathHeatTreeBernsteinUnflatten n L (pathHeatWienerMeshReindex g) = g := by
  ext p
  simp only [pathHeatTreeBernsteinUnflatten_apply,pathHeatWienerMeshReindex_apply,
    Equiv.symm_apply_apply]

theorem pathHeatTreeBernsteinUnflatten_basis (n L : ℕ) (p : Fin (L*(n+1))) :
    pathHeatTreeBernsteinUnflatten n L (EuclideanSpace.single p 1) =
      EuclideanSpace.single (finProdFinEquiv.symm p) 1 :=
  EuclideanSpace.piLpCongrLeft_single _ _ _

def pathHeatTreeBernsteinFlattenedSynthesis (n L : ℕ) :
    QuantitativePaper.Field (L*(n+1)) →L[ℝ] C(Fin L × I,ℝ) :=
  (pathHeatTreeBernsteinSynthesis n L).comp
    (pathHeatTreeBernsteinUnflatten n L).toContinuousLinearMap

theorem pathHeatTreeBernsteinFlattenedSynthesis_actualReindex (n L : ℕ)
    (g : EuclideanSpace ℝ (Fin L × Fin (n+1))) :
    pathHeatTreeBernsteinFlattenedSynthesis n L (pathHeatWienerMeshReindex g) =
      pathHeatTreeBernsteinSynthesis n L g := by
  change pathHeatTreeBernsteinSynthesis n L
    (pathHeatTreeBernsteinUnflatten n L (pathHeatWienerMeshReindex g)) = _
  rw [pathHeatTreeBernsteinUnflatten_actualReindex]

theorem pathHeatTreeBernsteinFlattenedSynthesis_basis (n L : ℕ)
    (p : Fin (L*(n+1))) :
    pathHeatTreeBernsteinFlattenedSynthesis n L (EuclideanSpace.single p 1) =
      pathHeatTreeBernsteinBasis n L (finProdFinEquiv.symm p) := by
  change pathHeatTreeBernsteinSynthesis n L
    (pathHeatTreeBernsteinUnflatten n L (EuclideanSpace.single p 1)) = _
  rw [pathHeatTreeBernsteinUnflatten_basis,pathHeatTreeBernsteinSynthesis_basis]

theorem norm_pathHeatTreeBernsteinFlattenedSynthesis_le (n L : ℕ) :
    ‖pathHeatTreeBernsteinFlattenedSynthesis n L‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simp only [one_mul]
  change ‖(pathHeatTreeBernsteinSynthesis n L) (pathHeatTreeBernsteinUnflatten n L g)‖ ≤ ‖g‖
  exact ((pathHeatTreeBernsteinSynthesis n L).le_opNorm _).trans
    (by
      simpa using mul_le_mul_of_nonneg_right
        (norm_pathHeatTreeBernsteinSynthesis_le n L)
        (norm_nonneg (pathHeatTreeBernsteinUnflatten n L g)))

theorem pathHeatTreeBernsteinFlattened_signed_covariance_contraction (n L : ℕ)
    (K : C(Fin L × I,C(Fin L × I,ℝ)))
    (M : SignedMeasure ((Fin L × I) × (Fin L × I))) :
    (∑p : Fin (L*(n+1)), ∑q : Fin (L*(n+1)),
      K ((finProdFinEquiv.symm p).1,bernstein.z (finProdFinEquiv.symm p).2)
        ((finProdFinEquiv.symm q).1,bernstein.z (finProdFinEquiv.symm q).2) *
        pathHeatSignedHessian M
          (pathHeatTreeBernsteinFlattenedSynthesis n L (EuclideanSpace.single p 1))
          (pathHeatTreeBernsteinFlattenedSynthesis n L (EuclideanSpace.single q 1))) =
      signedContraction
        (BoundedContinuousFunction.mkOfCompact (pathHeatTreeKernelSample n L K).uncurry) M := by
  rw [←finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  simp_rw [←finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply,pathHeatTreeBernsteinFlattenedSynthesis_basis]
  simpa only [pathHeatTreeBernsteinSynthesis_basis] using
    pathHeatTreeBernstein_signed_covariance_contraction n L K M

end HexagonPaper
