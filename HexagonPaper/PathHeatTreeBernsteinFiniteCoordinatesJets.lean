module
public import HexagonPaper.PathHeatTreeBernsteinFiniteCoordinates

@[expose] public section

/-! Full source signed jets extend to flat row paths through the actual
finite-coordinate terminal restriction. No derivative in an unused finite
row level is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace HexagonPaper
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X] [CompactSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y]

theorem pathHeatIndexPushforward_hessian_clm (ι : C(X,Y)) (M : SignedMeasure (X×X)) :
    pathHeatSignedHessian (M.map (pathHeatIndexPairMap ι)) =
      pathHeatPullbackHessian (pathHeatIndexRestriction ι) M := by
  ext h k
  exact pathHeatIndexPushforward_hessian ι M h k

theorem hasFDerivAt_pathHeatIndexExtensionScore (ι : C(X,Y))
    (S : C(X,ℝ) → SignedMeasure X) (M : C(X,ℝ) → SignedMeasure (X×X))
    (hS : ∀p, HasFDerivAt (fun q => pathHeatSignedScore (S q)) (pathHeatSignedHessian (M p)) p)
    (p : C(Y,ℝ)) :
    HasFDerivAt (fun q => pathHeatSignedScore ((S (pathHeatIndexRestriction ι q)).map ι))
      (pathHeatSignedHessian ((M (pathHeatIndexRestriction ι p)).map (pathHeatIndexPairMap ι))) p := by
  have he : (fun q => pathHeatSignedScore ((S (pathHeatIndexRestriction ι q)).map ι)) =
      fun q => pathHeatPullbackScore (pathHeatIndexRestriction ι) (S (pathHeatIndexRestriction ι q)) := by
    funext q
    exact pathHeatIndexPushforward_score_clm ι _
  rw [he,pathHeatIndexPushforward_hessian_clm]
  exact hasFDerivAt_pathHeatPullbackScore (pathHeatIndexRestriction ι) S M hS p

theorem pathHeatIndexExtension_second_fderiv (ι : C(X,Y))
    (f : C(X,ℝ) → ℝ) (S : C(X,ℝ) → SignedMeasure X) (M : C(X,ℝ) → SignedMeasure (X×X))
    (hf : ∀p, HasFDerivAt f (pathHeatSignedScore (S p)) p)
    (hS : ∀p, HasFDerivAt (fun q => pathHeatSignedScore (S q)) (pathHeatSignedHessian (M p)) p)
    (p h k : C(Y,ℝ)) :
    fderiv ℝ (fun u => fderiv ℝ (fun v => f (pathHeatIndexRestriction ι v)) u) p h k =
      pathHeatSignedHessian ((M (pathHeatIndexRestriction ι p)).map (pathHeatIndexPairMap ι)) h k := by
  rw [pathHeatIndexPushforward_hessian]
  exact pathHeatPullback_second_fderiv (pathHeatIndexRestriction ι) f S M hf hS p h k

theorem tendsto_pathHeatIndexExtension_tv (ι : C(X,Y))
    (S : C(X,ℝ) → SignedMeasure X) (p : C(Y,ℝ))
    (hS : Tendsto (fun q => signedTV (S q-S (pathHeatIndexRestriction ι p)))
      (𝓝 (pathHeatIndexRestriction ι p)) (𝓝 0)) :
    Tendsto (fun q => signedTV ((S (pathHeatIndexRestriction ι q)).map ι-
        (S (pathHeatIndexRestriction ι p)).map ι)) (𝓝 p) (𝓝 0) := by
  exact tendsto_pathHeatIndexPushforward_tv_sub (𝓝 p) ι
    (fun q => S (pathHeatIndexRestriction ι q)) (S (pathHeatIndexRestriction ι p))
    (hS.comp (pathHeatIndexRestriction ι).continuous.continuousAt.tendsto)

theorem pathHeatIndexRestriction_norm_apply_le (ι : C(X,Y)) (p : C(Y,ℝ)) :
    ‖pathHeatIndexRestriction ι p‖ ≤ ‖p‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg p)).mpr
  intro x
  exact p.norm_coe_le_norm (ι x)

theorem pathHeatIndexExtension_growth_bound (ι : C(X,Y))
    (f : C(X,ℝ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀p, |f p| ≤ C*(1+‖p‖)) (p : C(Y,ℝ)) :
    |f (pathHeatIndexRestriction ι p)| ≤ C*(1+‖p‖) :=
  (hf _).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (pathHeatIndexRestriction_norm_apply_le ι p)) hC)

theorem pathHeatIndexPushforward_kernel_pairing (ι : C(X,Y))
    (M : SignedMeasure (X×X)) (K : C(Y×Y,ℝ)) :
    pathHeatSignedScore (M.map (pathHeatIndexPairMap ι)) K =
      pathHeatSignedScore M (K.comp (pathHeatIndexPairMap ι)) :=
  pathHeatIndexPushforward_score (pathHeatIndexPairMap ι) M K

end HexagonPaper
