module
public import QuantitativePaper.VectorGradientTimeBounds
public import QuantitativePaper.VectorJointResponseSquareInterval

@[expose] public section

/-! Genuine finite-cell Hessian response representation and bounded smooth
terminal observables. This is the actual second field derivative of the
Cole--Hopf recursion, including its reaction term. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem boundedJets_vectorFieldHessian_component (s : RSBScheme k) (β t : ℝ)
    (j : ℕ) (i l : Fin n) :
    BoundedJets (fun z : VectorParameter n=>
      (vectorFieldHessian s β t z.1 j z.2 (EuclideanSpace.single i 1)) l) := by
  let F:=fun z : VectorParameter n=>vectorRecursion s β t z.1 j z.2
  let u:=vectorJointCoordinateDirection n i
  let v:=vectorJointCoordinateDirection n l
  have hB:=((boundedPositiveJets_vectorRecursion_joint s β t j).fderiv_apply v).boundedJets_fderiv_apply u
  have hDF : Differentiable ℝ (fderiv ℝ F):=
    ((contDiff_vectorRecursion_joint s β t j).fderiv_right (m:=∞) (by simp)).differentiable (by simp)
  have he : (fun z : VectorParameter n=>
      (vectorFieldHessian s β t z.1 j z.2 (EuclideanSpace.single i 1)) l)=
      (fun z=>fderiv ℝ (fun y=>fderiv ℝ F y v) z u) := by
    funext z
    rw [vectorFieldHessian_component_eq_joint]
    rw [fderiv_clm_apply (hDF z) (differentiableAt_const v)]
    rw [show fderiv ℝ (fun _ : VectorParameter n=>v) z=0 from (hasFDerivAt_const v z).fderiv]
    simp only [fderiv_const,ContinuousLinearMap.comp_zero,zero_add,
      ContinuousLinearMap.flip_apply]
    rfl
  rw [he]
  exact hB

def vectorFiniteHessianResponseObservable (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (l : Fin n) (z : VectorParameter n) : ℝ :=
  (vectorFieldHessian s β t z.1 (k+1-i) z.2 (EuclideanSpace.single l 1)) l+
    s.m i*(vectorMagnetization s β t z.1 (k+1-i) z.2 l)^2

theorem boundedJets_vectorFiniteHessianResponseObservable (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (l : Fin n) : BoundedJets (vectorFiniteHessianResponseObservable s β t i l) := by
  have hM:=boundedJets_vectorMagnetization_component s β t (k+1-i) l
  unfold vectorFiniteHessianResponseObservable
  simpa only [pow_two] using
    (boundedJets_vectorFieldHessian_component s β t (k+1-i) l l).add
      ((hM.mul hM).const_mul (s.m i))

def vectorFiniteHessianResponseData (s : RSBScheme k) (β t : ℝ) (i : ℕ) (l : Fin n) :
    VectorJointResponseTestData
      (fun z : VectorParameter n=>vectorRecursion s β t z.1 (k+1-i) z.2)
      (vectorFiniteHessianResponseObservable s β t i l) := by
  let h:=boundedJets_vectorFiniteHessianResponseObservable s β t i l
  let B:=fun j=>Classical.choose (h.2 j)
  exact vectorRecursionJointResponseData s β t (k+1-i) {
    regularity := h.1.of_le (by simp)
    bounds := B
    bounds_nonneg := fun j=>(Classical.choose_spec (h.2 j)).1
    jets := fun j _=>(Classical.choose_spec (h.2 j)).2 }

theorem hessianOperator_euclidean_diagonal (f : Field n→ℝ) (x : Field n) (l : Fin n) :
    (hessianOperator f x (EuclideanSpace.single l 1)) l=
      directionalHessian f x (EuclideanSpace.single l 1) := by
  rw [directionalHessian,←inner_hessianOperator]
  simp only [EuclideanSpace.inner_single_right,one_mul,starRingEnd_apply,star_trivial]

theorem vectorFiniteCellHessian_diagonal_eq_response (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (q : ℝ) (x : Field n) (l : Fin n) :
    (hessianOperator (vectorFiniteCellPotential s β t p i q) x (EuclideanSpace.single l 1)) l=
      vectorStepResponse ((1-t)*β^2*(s.q (i+1)-q)) (s.m i)
        (vectorRecursion s β t p (k+1-i))
        (fun y=>vectorFiniteHessianResponseObservable s β t i l (p,y)) x-
      s.m i*(gradient (vectorFiniteCellPotential s β t p i q) x l)^2 := by
  rw [hessianOperator_euclidean_diagonal]
  have he:=vectorStepResponse_recursion_heat_generator s β t
    ((1-t)*β^2*(s.q (i+1)-q)) (s.m i) p (k+1-i) x l
  rw [←gradient_euclidean_coordinate] at he
  change _=directionalHessian (vectorFiniteCellPotential s β t p i q) x (EuclideanSpace.single l 1)+
    s.m i*(gradient (vectorFiniteCellPotential s β t p i q) x l)^2 at he
  change _=vectorStepResponse _ _ _ _ _-_
  simp only [vectorFiniteHessianResponseObservable]
  rw [he]
  ring

end QuantitativePaper
