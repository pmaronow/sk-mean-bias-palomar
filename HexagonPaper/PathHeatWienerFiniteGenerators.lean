module
public import HexagonPaper.PathHeatSignedSourceFiniteGenerators
public import HexagonPaper.PathHeatClockKernel

@[expose] public section

/-! The clock covariance of actual finite Wiener observations contracts
to the actual sampled mixed path kernel. No covariance or response identity
is supplied as a hypothesis. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators unitInterval BoundedContinuousFunction
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup FourPapersCommon
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {L n : ℕ}

def pathHeatWienerFiniteKernel (n L : ℕ) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (dc : ℝ→Fin L→C(I,ℝ)) (z : ℝ) : ((Fin L×I)×(Fin L×I))→ᵇℝ :=
  BoundedContinuousFunction.mkOfCompact
    (pathHeatTreeMixedKernelOperator δ W (pathHeatTreeKernelSample n L (pathHeatClockRawKernel (dc z)))).uncurry

theorem pathHeatWienerFinite_density_generator
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (dc : ℝ→Fin L→C(I,ℝ))
    (dotell : ℝ×C(Fin L×I,ℝ)→ℝ)
    (S : ℝ×C(Fin L×I,ℝ)→SignedMeasure (Fin L×I))
    (M : ℝ×C(Fin L×I,ℝ)→SignedMeasure ((Fin L×I)×(Fin L×I)))
    (z : ℝ) (h0 : ∀l,dc z l 0=0) (y : QuantitativePaper.Field (L*(n+1))) :
    pathHeatSourceFiniteDensityGenerator (pathHeatTreeMixedFlattenedSynthesis n L δ W)
      dotell S M (pathHeatClockMeshDerivative n dc) pathHeatBrownianClockMask z y=
      pathHeatDensityGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
        (S (z,pathHeatTreeMixedFlattenedSynthesis n L δ W y))
        (M (z,pathHeatTreeMixedFlattenedSynthesis n L δ W y))
        (dotell (z,pathHeatTreeMixedFlattenedSynthesis n L δ W y)) := by
  unfold pathHeatSourceFiniteDensityGenerator pathHeatDensityGenerator
  simp_rw [pathHeatClockMesh_covarianceDerivative n dc z h0]
  rw [pathHeatTreeMixedFlattened_signed_covariance_contraction]
  rfl

theorem pathHeatWienerFinite_observable_generator
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (dc : ℝ→Fin L→C(I,ℝ))
    (dotPhi : ℝ×C(Fin L×I,ℝ)→ℝ)
    (S P : ℝ×C(Fin L×I,ℝ)→SignedMeasure (Fin L×I))
    (Q : ℝ×C(Fin L×I,ℝ)→SignedMeasure ((Fin L×I)×(Fin L×I)))
    (z : ℝ) (h0 : ∀l,dc z l 0=0) (y : QuantitativePaper.Field (L*(n+1))) :
    pathHeatSourceFiniteObservableGenerator (pathHeatTreeMixedFlattenedSynthesis n L δ W)
      dotPhi S P Q (pathHeatClockMeshDerivative n dc) pathHeatBrownianClockMask z y=
      pathHeatObservableGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
        (S (z,pathHeatTreeMixedFlattenedSynthesis n L δ W y))
        (P (z,pathHeatTreeMixedFlattenedSynthesis n L δ W y))
        (Q (z,pathHeatTreeMixedFlattenedSynthesis n L δ W y))
        (dotPhi (z,pathHeatTreeMixedFlattenedSynthesis n L δ W y)) := by
  unfold pathHeatSourceFiniteObservableGenerator pathHeatObservableGenerator
  simp_rw [pathHeatClockMesh_covarianceDerivative n dc z h0]
  rw [pathHeatTreeMixedFlattened_signed_covariance_contraction]
  rfl

end HexagonPaper
