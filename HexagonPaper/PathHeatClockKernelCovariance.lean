module
public import HexagonPaper.PathHeatClockKernel

@[expose] public section

/-! Identification of the continuous raw clock kernel with the covariance
of the actual native Wiener mesh law and its actual independent-increment
Gaussian factor. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped unitInterval Topology BigOperators
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem pathHeatClock_min_covariance {L : ℕ} (c : Fin L → C(I,I))
    (hc : ∀l, Monotone (c l)) (l : Fin L) (t u : I) :
    min (c l t : ℝ) (c l u : ℝ) = (c l (min t u) : ℝ) := by
  have h : c l (min t u) = min (c l t) (c l u) := (hc l).map_min
  exact (congrArg (fun x : I => (x:ℝ)) h).symm

theorem pathHeatClockMesh_covariance (n : ℕ) {L : ℕ}
    (c : ℝ → Fin L → C(I,I)) (z : ℝ)
    (hc : ∀l, Monotone (c z l)) (h0 : ∀l, c z l 0=0)
    (p q : Fin (L*(n+1))) :
    pathHeatVarianceCovariance (pathHeatBrownianClockVariance (pathHeatClockMesh n c))
      pathHeatBrownianClockMask z p q =
        pathHeatClockRawKernel (pathHeatClockReal (c z))
          ((finProdFinEquiv.symm p).1,bernstein.z (finProdFinEquiv.symm p).2)
          ((finProdFinEquiv.symm q).1,bernstein.z (finProdFinEquiv.symm q).2) := by
  rw [pathHeatBrownianClock_covariance (pathHeatClockMesh n c) z
    (fun a => (hc a).comp (bernstein_z_monotone n))
    (fun a => by
      change (c z a (bernstein.z 0) : ℝ)=0
      rw [bernstein.z_zero,h0]
      rfl)]
  rw [pathHeatClockRawKernel_apply]
  by_cases hpq : (finProdFinEquiv.symm p).1=(finProdFinEquiv.symm q).1
  · simp only [hpq,ite_true,pathHeatClockMesh,pathHeatClockReal_apply]
    exact pathHeatClock_min_covariance (c z) hc _ _ _
  · simp only [hpq,ite_false]

theorem pathHeatClockMesh_actualCovariance (n : ℕ) {L : ℕ}
    (c : ℝ → Fin L → C(I,I)) (z : ℝ) (hc : ∀l, Monotone (c z l))
    (p q : Fin (L*(n+1))) :
    covarianceBilin (pathHeatWienerMeshReindexedLaw (pathHeatClockMesh n c z))
      (EuclideanSpace.single p 1) (EuclideanSpace.single q 1) =
        pathHeatClockRawKernel (pathHeatClockReal (c z))
          ((finProdFinEquiv.symm p).1,bernstein.z (finProdFinEquiv.symm p).2)
          ((finProdFinEquiv.symm q).1,bernstein.z (finProdFinEquiv.symm q).2) := by
  rw [pathHeatWienerMeshReindexedLaw_covariance,pathHeatClockRawKernel_apply]
  by_cases hpq : (finProdFinEquiv.symm p).1=(finProdFinEquiv.symm q).1
  · simp only [hpq,ite_true,pathHeatClockMesh,pathHeatClockReal_apply]
    exact pathHeatClock_min_covariance (c z) hc _ _ _
  · simp only [hpq,ite_false]

end HexagonPaper
