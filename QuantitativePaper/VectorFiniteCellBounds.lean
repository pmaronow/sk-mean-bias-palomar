module
public import QuantitativePaper.VectorFiniteCellPDE
public import QuantitativePaper.VectorBackwardLinear

@[expose] public section

/-! Depth-independent bounds for the actual finite-cell time generator.
They use the genuine conditional-spin covariance sandwich and spin squares
equal to one, rather than a supplied Hessian bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000

theorem vectorFieldHessian_diagonal_bounds {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) (i : Fin n) :
    0 ≤ (vectorFieldHessian s β t p j x (EuclideanSpace.single i (1 : ℝ))) i ∧
    (vectorFieldHessian s β t p j x (EuclideanSpace.single i (1 : ℝ))) i+
      (vectorMagnetization s β t p j x i)^2 ≤ 1 := by
  have hn := vectorFieldHessian_quadratic_nonneg s β t p j x (EuclideanSpace.single i (1 : ℝ))
  have hu := (vectorFieldHessian_covariance_quadratic_bounds s β t p j x
    (EuclideanSpace.single i (1 : ℝ))).2
  have he : (fun σ : Configuration n => fieldDot (EuclideanSpace.single i (1 : ℝ)) σ)=
      fun σ => Paper.spinSign (σ i) := by funext σ;simp [fieldDot]
  rw [he] at hu
  have hs : (fun σ : Configuration n => (Paper.spinSign (σ i))^2)=fun _ => (1 : ℝ) := by
    funext σ
    simp
  unfold vectorObservableCovariance at hu
  rw [hs,vectorConditionalMean_const] at hu
  simp only [EuclideanSpace.inner_single_left,map_one,one_mul] at hn hu
  refine ⟨hn,?_⟩
  change (vectorFieldHessian s β t p j x (EuclideanSpace.single i (1 : ℝ))) i+
    (vectorObservableResponse s β t p (fun σ => Paper.spinSign (σ i)) j 0 x)^2 ≤ 1
  linarith

theorem vectorRecursion_coordinate_generator_bounds {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (m : ℝ) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (x : Field n) (i : Fin n) :
    0 ≤ (vectorFieldHessian s β t p j x (EuclideanSpace.single i (1 : ℝ))) i+
      m*(vectorMagnetization s β t p j x i)^2 ∧
    (vectorFieldHessian s β t p j x (EuclideanSpace.single i (1 : ℝ))) i+
      m*(vectorMagnetization s β t p j x i)^2 ≤ 1 := by
  have h := vectorFieldHessian_diagonal_bounds s β t p j x i
  refine ⟨add_nonneg h.1 (mul_nonneg hm0 (sq_nonneg _)),?_⟩
  have hh := mul_le_mul_of_nonneg_right hm1 (sq_nonneg (vectorMagnetization s β t p j x i))
  nlinarith

theorem vectorStepResponse_recursion_heat_bounds {n k : ℕ} (s : RSBScheme k)
    (β t c m : ℝ) (p : Couplings n × ℝ) (j : ℕ)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (x : Field n) (i : Fin n) :
    0 ≤ vectorStepResponse c m (vectorRecursion s β t p j)
      (fun y => (vectorFieldHessian s β t p j y (EuclideanSpace.single i (1 : ℝ))) i+
        m*(vectorMagnetization s β t p j y i)^2) x ∧
    vectorStepResponse c m (vectorRecursion s β t p j)
      (fun y => (vectorFieldHessian s β t p j y (EuclideanSpace.single i (1 : ℝ))) i+
        m*(vectorMagnetization s β t p j y i)^2) x ≤ 1 := by
  let G := fun y => (vectorFieldHessian s β t p j y (EuclideanSpace.single i (1 : ℝ))) i+
    m*(vectorMagnetization s β t p j y i)^2
  have hG (y : Field n) : 0 ≤ G y ∧ G y ≤ 1 := vectorRecursion_coordinate_generator_bounds s β t p j m hm0 hm1 y i
  have hm : Measurable G := by
    apply Measurable.add
    · exact ((continuous_vectorFieldHessian_component s β t j i i).comp
        (continuous_const.prodMk continuous_id)).measurable
    · exact measurable_const.mul (((boundedJets_vectorMagnetization_component s β t j i).1.continuous.comp
        (continuous_const.prodMk continuous_id)).measurable.pow_const 2)
  have hf := vectorRecursion_lipschitz s β t p j
  refine ⟨vectorStepResponse_nonneg _ G _ hf (fun y => (hG y).1) c m x,?_⟩
  have hh := vectorStepResponse_mono _ G (fun _ => (1 : ℝ)) _ hf hm measurable_const 1 1
    (fun y => by rw [abs_of_nonneg (hG y).1];exact (hG y).2)
    (fun _ => by norm_num) (fun y => (hG y).2) c m x
  rw [vectorStepResponse_const _ _ hf c m 1 x] at hh
  exact hh

theorem vectorFiniteCellPotential_time_deriv_bounds {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (p : Couplings n × ℝ)
    (i : ℕ) (hi : i ≤ k+1) (q : ℝ) (hq : q<s.q (i+1)) (x : Field n) :
    -((1-t)*β^2)*(n : ℝ)/2 ≤ deriv (fun r => vectorFiniteCellPotential s β t p i r x) q ∧
    deriv (fun r => vectorFiniteCellPotential s β t p i r x) q ≤ 0 := by
  rw [(hasDerivAt_vectorFiniteCellPotential_time s β t hβ ht p i q hq x).deriv]
  let S := ∑l : Fin n,vectorStepResponse ((1-t)*β^2*(s.q (i+1)-q)) (s.m i)
    (vectorRecursion s β t p (k+1-i))
    (fun y => (vectorFieldHessian s β t p (k+1-i) y (EuclideanSpace.single l (1 : ℝ))) l+
      s.m i*(vectorMagnetization s β t p (k+1-i) y l)^2) x
  have hb (l : Fin n) := vectorStepResponse_recursion_heat_bounds s β t
    ((1-t)*β^2*(s.q (i+1)-q)) (s.m i) p (k+1-i)
    (s.m_nonneg hi) (s.m_le_one hi) x l
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun l _ => (hb l).1
  have hS1 : S ≤ (n : ℝ) := by
    exact (Finset.sum_le_sum fun l _ => (hb l).2).trans_eq (by simp)
  have hc : 0 ≤ (1-t)*β^2 := mul_nonneg (sub_nonneg.mpr ht.le) (sq_nonneg β)
  change -((1-t)*β^2)/2*S≥-((1-t)*β^2)*(n : ℝ)/2 ∧ -((1-t)*β^2)/2*S ≤ 0
  constructor
  · nlinarith
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hS0

end QuantitativePaper
