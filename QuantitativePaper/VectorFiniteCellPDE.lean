module
public import QuantitativePaper.VectorFiniteCells
public import QuantitativePaper.VectorSpatialStep

@[expose] public section

/-! The literal finite-cell vector Parisi PDE. The Laplacian and gradient in
the conclusion are constructed from the actual Frechet derivatives of the
Gaussian Cole--Hopf potential, rather than supplied fields. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def vectorLaplacian {n : ℕ} (f : Field n → ℝ) (x : Field n) : ℝ :=
  ∑i : Fin n,directionalHessian f x (EuclideanSpace.single i (1 : ℝ))

theorem gradient_euclidean_coordinate {n : ℕ} (f : Field n → ℝ)
    (x : Field n) (i : Fin n) :
    gradient f x i=fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) := by
  simpa only [EuclideanSpace.inner_single_right,starRingEnd_apply,star_trivial,one_mul] using
    (inner_gradient_left (f := f) (x := x) (y := EuclideanSpace.single i (1 : ℝ)))

theorem vectorStepResponse_recursion_heat_generator {n k : ℕ} (s : RSBScheme k)
    (β t c m : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) (i : Fin n) :
    vectorStepResponse c m (vectorRecursion s β t p j)
      (fun y => (vectorFieldHessian s β t p j y (EuclideanSpace.single i (1 : ℝ))) i+
        m*(vectorMagnetization s β t p j y i)^2) x=
      directionalHessian (vectorColeHopfStep c m (vectorRecursion s β t p j)) x
        (EuclideanSpace.single i (1 : ℝ))+
      m*(fderiv ℝ (vectorColeHopfStep c m (vectorRecursion s β t p j)) x
        (EuclideanSpace.single i (1 : ℝ)))^2 := by
  have hf := vectorRecursion_lipschitz s β t p j
  have hH : Measurable (fun y => (vectorFieldHessian s β t p j y (EuclideanSpace.single i (1 : ℝ))) i) :=
    ((continuous_vectorFieldHessian_component s β t j i i).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hv : Measurable (fun y => vectorMagnetization s β t p j y i) :=
    ((boundedJets_vectorMagnetization_component s β t j i).1.continuous.comp
      (continuous_const.prodMk continuous_id)).measurable
  obtain ⟨H,hH0,hBound⟩ := exists_vectorFieldHessian_component_bound (n := n) s β t j
  have hbv (y : Field n) : |m*(vectorMagnetization s β t p j y i)^2| ≤ |m| := by
    rw [abs_mul,abs_sq]
    have hh := vectorMagnetization_component_bound s β t p j y i
    have hs := mul_self_le_mul_self (abs_nonneg _) hh
    simpa only [one_pow,mul_one,←pow_two,sq_abs] using mul_le_mul_of_nonneg_left hs (abs_nonneg m)
  have hmv : Measurable (fun y => m*(vectorMagnetization s β t p j y i)^2) :=
    measurable_const.mul (hv.pow_const 2)
  have hsplit := vectorStepResponse_add (vectorRecursion s β t p j)
    (fun y => (vectorFieldHessian s β t p j y (EuclideanSpace.single i (1 : ℝ))) i)
    (fun y => m*(vectorMagnetization s β t p j y i)^2) _ hf hH hmv H (|m|)
    (fun y => hBound (p,y) i i) hbv c m x
  rw [hsplit,vectorStepResponse_mul_const,
    directionalHessian_vectorColeHopfStep_recursion_coordinate,
    fderiv_vectorColeHopfStep_recursion_coordinate]
  unfold vectorStepSecondResponse
  ring

theorem hasDerivAt_vectorFiniteCellPotential_PDE {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (p : Couplings n × ℝ)
    (i : ℕ) (q : ℝ) (hq : q<s.q (i+1)) (x : Field n) :
    HasDerivAt (fun r => vectorFiniteCellPotential s β t p i r x)
      (-((1-t)*β^2)/2*
        (vectorLaplacian (vectorFiniteCellPotential s β t p i q) x+
          s.m i*‖gradient (vectorFiniteCellPotential s β t p i q) x‖^2)) q := by
  have hh := hasDerivAt_vectorFiniteCellPotential_time s β t hβ ht p i q hq x
  apply hh.congr_deriv
  congr 1
  simp_rw [vectorStepResponse_recursion_heat_generator]
  rw [Finset.sum_add_distrib]
  simp_rw [←gradient_euclidean_coordinate]
  rw [←Finset.mul_sum,←EuclideanSpace.real_norm_sq_eq]
  rfl

end QuantitativePaper
