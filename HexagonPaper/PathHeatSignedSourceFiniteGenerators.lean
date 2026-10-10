module
public import HexagonPaper.PathHeatSignedSourceFiniteResponse
public import HexagonPaper.PathHeatSignedGenerators

@[expose] public section

/-! Exact uncentered signed generators of the source finite response.
All signed measures are evaluated at the actual interpolated path; the
Gaussian covariance direction is the literal half-double basis sum. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators NNReal
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup FourPapersCommon
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]
variable {n m : ℕ}

def pathHeatSourceFiniteDensityGenerator (A : Field m→L[ℝ]C(X,ℝ))
    (dotell : ℝ×C(X,ℝ)→ℝ) (S : ℝ×C(X,ℝ)→SignedMeasure X)
    (M : ℝ×C(X,ℝ)→SignedMeasure (X×X))
    (dv : ℝ→Fin n→ℝ) (mask : Fin n→Field m) (u : ℝ) (y : Field m) : ℝ :=
  dotell (u,A y)+(1/2:ℝ)*∑j : Fin m,∑k : Fin m,
    pathHeatVarianceCovarianceDerivative dv mask u j k*
      pathHeatSignedHessian (pathHeatDensityDerivativeMeasure (S (u,A y)) (M (u,A y)))
        (A (EuclideanSpace.single j 1)) (A (EuclideanSpace.single k 1))

def pathHeatSourceFiniteObservableGenerator (A : Field m→L[ℝ]C(X,ℝ))
    (dotPhi : ℝ×C(X,ℝ)→ℝ) (S P : ℝ×C(X,ℝ)→SignedMeasure X)
    (Q : ℝ×C(X,ℝ)→SignedMeasure (X×X))
    (dv : ℝ→Fin n→ℝ) (mask : Fin n→Field m) (u : ℝ) (y : Field m) : ℝ :=
  dotPhi (u,A y)+(1/2:ℝ)*∑j : Fin m,∑k : Fin m,
    pathHeatVarianceCovarianceDerivative dv mask u j k*
      pathHeatSignedHessian (pathHeatObservableDerivativeMeasure (S (u,A y)) (P (u,A y)) (Q (u,A y)))
        (A (EuclideanSpace.single j 1)) (A (EuclideanSpace.single k 1))

theorem pathHeat_source_finite_density_score_eq_generator
    (A : Field m→L[ℝ]C(X,ℝ)) (ell : ℝ→C(X,ℝ)→ℝ) (dotell : ℝ×C(X,ℝ)→ℝ)
    (S : ℝ×C(X,ℝ)→SignedMeasure X) (M : ℝ×C(X,ℝ)→SignedMeasure (X×X))
    (u : ℝ)
    (hf : ∀p,HasFDerivAt (ell u) (pathHeatSignedScore (S (u,p))) p)
    (hS : ∀p,HasFDerivAt (fun q=>pathHeatSignedScore (S (u,q))) (pathHeatSignedHessian (M (u,p))) p)
    (dv : ℝ→Fin n→ℝ) (mask : Fin n→Field m) (y : Field m) :
    pathHeatSourceFiniteDensityScore A ell dotell dv mask u y=
      pathHeatSourceFiniteDensityGenerator A dotell S M dv mask u y := by
  have hs := (hasFDerivAt_pathHeatPullback A (ell u) (fun p=>S (u,p)) hf y).fderiv
  unfold pathHeatSourceFiniteDensityScore pathHeatSourceFiniteDensityGenerator
  have hjet (j k : Fin m) : vectorHessian (fun z=>ell u (A z)) y
      (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)+
      fderiv ℝ (fun z=>ell u (A z)) y (EuclideanSpace.single j 1)*
        fderiv ℝ (fun z=>ell u (A z)) y (EuclideanSpace.single k 1)=
      pathHeatSignedHessian (pathHeatDensityDerivativeMeasure (S (u,A y)) (M (u,A y)))
        (A (EuclideanSpace.single j 1)) (A (EuclideanSpace.single k 1)) := by
    rw [vectorHessian,pathHeatPullback_second_fderiv A (ell u)
      (fun p=>S (u,p)) (fun p=>M (u,p)) hf hS,hs]
    rw [pathHeatDensityDerivativeMeasure,pathHeatSignedHessian_add]
    simp only [ContinuousLinearMap.add_apply]
    rw [pathHeatSignedHessian_tensor]
    rfl
  simp_rw [hjet]

theorem pathHeat_source_finite_centered_score_eq_generators
    (A : Field m→L[ℝ]C(X,ℝ)) (ell Phi : ℝ→C(X,ℝ)→ℝ)
    (dotell dotPhi : ℝ×C(X,ℝ)→ℝ)
    (S P : ℝ×C(X,ℝ)→SignedMeasure X) (M Q : ℝ×C(X,ℝ)→SignedMeasure (X×X))
    (u : ℝ)
    (hf : ∀p,HasFDerivAt (ell u) (pathHeatSignedScore (S (u,p))) p)
    (hg : ∀p,HasFDerivAt (Phi u) (pathHeatSignedScore (P (u,p))) p)
    (hS : ∀p,HasFDerivAt (fun q=>pathHeatSignedScore (S (u,q))) (pathHeatSignedHessian (M (u,p))) p)
    (hP : ∀p,HasFDerivAt (fun q=>pathHeatSignedScore (P (u,q))) (pathHeatSignedHessian (Q (u,p))) p)
    (dv : ℝ→Fin n→ℝ) (mask : Fin n→Field m) (y : Field m) (center : ℝ) :
    pathHeatSourceFiniteCenteredScore A ell Phi dotell dotPhi dv mask u y center=
      pathHeatSourceFiniteObservableGenerator A dotPhi S P Q dv mask u y+
        (Phi u (A y)-center)*pathHeatSourceFiniteDensityGenerator A dotell S M dv mask u y := by
  unfold pathHeatSourceFiniteCenteredScore pathHeatSourceFiniteObservableGenerator pathHeatSourceFiniteDensityGenerator
  simp_rw [pathHeat_finiteGaussianScoreBilinear A (ell u) (Phi u)
    (fun p=>S (u,p)) (fun p=>P (u,p)) (fun p=>M (u,p)) (fun p=>Q (u,p)) hf hg hS hP]
  have hterm (j k : Fin m) : pathHeatVarianceCovarianceDerivative dv mask u j k*
      pathHeatSignedHessian
        (pathHeatCenteredDerivativeMeasure (S (u,A y)) (P (u,A y)) (M (u,A y)) (Q (u,A y)) (Phi u (A y)) center)
        (A (EuclideanSpace.single j 1)) (A (EuclideanSpace.single k 1))=
      pathHeatVarianceCovarianceDerivative dv mask u j k*
        pathHeatSignedHessian (pathHeatObservableDerivativeMeasure (S (u,A y)) (P (u,A y)) (Q (u,A y)))
          (A (EuclideanSpace.single j 1)) (A (EuclideanSpace.single k 1))+
      (Phi u (A y)-center)*(pathHeatVarianceCovarianceDerivative dv mask u j k*
        pathHeatSignedHessian (pathHeatDensityDerivativeMeasure (S (u,A y)) (M (u,A y)))
          (A (EuclideanSpace.single j 1)) (A (EuclideanSpace.single k 1))) := by
    simp only [pathHeatCenteredDerivativeMeasure,pathHeatDensityDerivativeMeasure,
      pathHeatObservableDerivativeMeasure,pathHeatSignedHessian_add,pathHeatSignedHessian_smul,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  ring

theorem pathHeat_signed_source_finite_generator_response
    (a b : ℝ) (hab : a≤b) (z : ℝ) (hz : z∈Ioo a b)
    (A : Field m→L[ℝ]C(X,ℝ))
    (ell Phi : ℝ→C(X,ℝ)→ℝ) (dotell dotPhi : ℝ×C(X,ℝ)→ℝ)
    (S P : ℝ×C(X,ℝ)→SignedMeasure X) (M Q : ℝ×C(X,ℝ)→SignedMeasure (X×X))
    (B Ls Lm Lp Lq C0 C1 Dt Dphi : ℝ≥0)
    (hs : PathHeatSignedSpatialBounds ell Phi S P M Q (Icc a b) B Ls Lm Lp Lq C0 C1)
    (ht : PathHeatSignedParameterData ell dotell S (Ioo a b))
    (hp : PathHeatSignedParameterData Phi dotPhi P (Ioo a b))
    (hdt : ∀u∈Ioo a b,∀p,|dotell (u,p)|≤Dt)
    (hdphi : ∀u∈Ioo a b,∀p,|dotPhi (u,p)|≤Dphi)
    (v dv : ℝ→Fin n→ℝ) (mask : Fin n→Field m)
    (hv : ∀u∈Ioo a b,∀i,0<v u i)
    (hdv : ∀u∈Ioo a b,∀i,HasDerivAt (fun t=>v t i) (dv u i) u)
    (hdvc : ∀i,ContinuousAt (fun u=>dv u i) z) (x : Field m) :
    let Y := fun g : Field n=>x+pathHeatVarianceFactor v mask z g
    let H := pathHeatSourceFiniteDensityGenerator A dotell S M dv mask z
    let J := pathHeatSourceFiniteObservableGenerator A dotPhi S P Q dv mask z
    0<pathHeatSourceFiniteNormalizer A ell v mask x z ∧
    HasDerivAt (pathHeatSourceFiniteNormalizer A ell v mask x)
      (∫g,Real.exp (ell z (A (Y g)))*H (Y g) ∂fieldGaussian n) z ∧
    HasDerivAt (pathHeatSourceFiniteNumerator A ell Phi v mask x)
      (∫g,Real.exp (ell z (A (Y g)))*(J (Y g)+Phi z (A (Y g))*H (Y g)) ∂fieldGaussian n) z ∧
    HasDerivAt (pathHeatSourceFiniteExpectation A ell Phi v mask x)
      ((∫g,Real.exp (ell z (A (Y g)))*(J (Y g)+
        (Phi z (A (Y g))-pathHeatSourceFiniteExpectation A ell Phi v mask x z)*H (Y g))
          ∂fieldGaussian n)/pathHeatSourceFiniteNormalizer A ell v mask x z) z := by
  dsimp only
  have hr := pathHeat_signed_source_finite_response a b hab z hz A ell Phi dotell dotPhi S P M Q
    B Ls Lm Lp Lq C0 C1 Dt Dphi hs ht hp hdt hdphi v dv mask hv hdv hdvc x
  have hz' : z∈Icc a b := ⟨hz.1.le,hz.2.le⟩
  have hH (y : Field m) := pathHeat_source_finite_density_score_eq_generator A ell dotell S M z
    (hs.ell_derivative z hz') (hs.score_derivative z hz') dv mask y
  have hJ (y : Field m) (center : ℝ) := pathHeat_source_finite_centered_score_eq_generators
    A ell Phi dotell dotPhi S P M Q z (hs.ell_derivative z hz') (hs.phi_derivative z hz')
      (hs.score_derivative z hz') (hs.phi_score_derivative z hz') dv mask y center
  refine ⟨hr.1,?_,?_,?_⟩
  · apply hr.2.1.congr_deriv
    apply integral_congr_ae
    exact .of_forall fun g=>by dsimp only;rw [hH]
  · apply hr.2.2.1.congr_deriv
    apply integral_congr_ae
    exact .of_forall fun g=>by dsimp only;rw [hJ];simp only [sub_zero]
  · apply hr.2.2.2.congr_deriv
    congr 1
    apply integral_congr_ae
    exact .of_forall fun g=>by dsimp only;rw [hJ]

end HexagonPaper
