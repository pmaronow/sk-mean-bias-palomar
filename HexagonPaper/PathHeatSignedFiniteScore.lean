module
public import HexagonPaper.PathHeatSignedTensorJet
public import HexagonPaper.PathHeatSignedJetPullback
public import HexagonPaper.PathHeatFinitePrice

@[expose] public section

/-! The finite Gaussian centered score is the exact pullback of the
manuscript's signed Hessian bundle. The derivative measures are the actual
ones at the interpolated path; they are never replaced by grid masses. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup FourPapersCommon
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]
variable {n : ℕ}

theorem pathHeat_finiteGaussianScoreBilinear
    (A : QuantitativePaper.Field n→L[ℝ]C(X,ℝ)) (f g : C(X,ℝ)→ℝ)
    (S P : C(X,ℝ)→SignedMeasure X) (M Q : C(X,ℝ)→SignedMeasure (X×X))
    (hf : ∀p,HasFDerivAt f (pathHeatSignedScore (S p)) p)
    (hg : ∀p,HasFDerivAt g (pathHeatSignedScore (P p)) p)
    (hS : ∀p,HasFDerivAt (fun q=>pathHeatSignedScore (S q)) (pathHeatSignedHessian (M p)) p)
    (hP : ∀p,HasFDerivAt (fun q=>pathHeatSignedScore (P q)) (pathHeatSignedHessian (Q p)) p)
    (y h k : QuantitativePaper.Field n) (center : ℝ) :
    gaussianScoreBilinear (fun u=>f (A u)) (fun u=>g (A u)) y h k center=
      pathHeatSignedHessian
        (pathHeatCenteredDerivativeMeasure (S (A y)) (P (A y)) (M (A y)) (Q (A y)) (g (A y)) center)
          (A h) (A k) := by
  have hs := (hasFDerivAt_pathHeatPullback A f S hf y).fderiv
  have hp := (hasFDerivAt_pathHeatPullback A g P hg y).fderiv
  unfold gaussianScoreBilinear vectorHessian
  rw [pathHeatPullback_second_fderiv A g P Q hg hP,
    pathHeatPullback_second_fderiv A f S M hf hS,hs,hp,
      pathHeatCenteredDerivativeMeasure_hessian]
  simp only [pathHeatPullbackScore,ContinuousLinearMap.comp_apply,pathHeatSignedHessian_apply]
  ring

end HexagonPaper
