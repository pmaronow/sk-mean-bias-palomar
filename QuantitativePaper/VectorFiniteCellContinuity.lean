module
public import QuantitativePaper.VectorResponseContinuity
public import QuantitativePaper.VectorFiniteCellBounds
public import QuantitativePaper.VectorUniformVarianceJets
public import QuantitativePaper.VectorGradientBounds

@[expose] public section

/-! Genuine joint time/space continuity of the finite-cell first derivatives,
Laplacian entries and time generator. No time derivative at zero variance is
assumed. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 400000

def vectorFiniteCellTimeField {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (q : ℝ) (x : Field n) : ℝ :=
  -((1-t)*β^2)/2*∑l : Fin n,
    vectorStepResponse ((1-t)*β^2*(s.q (i+1)-q)) (s.m i)
      (vectorRecursion s β t p (k+1-i))
      (fun y => (vectorFieldHessian s β t p (k+1-i) y (EuclideanSpace.single l (1 : ℝ))) l+
        s.m i*(vectorMagnetization s β t p (k+1-i) y l)^2) x

theorem continuous_vectorFiniteCellPotential_gradient_coordinate {n k : ℕ}
    (s : RSBScheme k) (β t : ℝ) (p : Couplings n×ℝ) (i : ℕ) (l : Fin n) :
    Continuous (fun z : ℝ×Field n =>
      gradient (vectorFiniteCellPotential s β t p i z.1) z.2 l) := by
  let g := fun y : Field n => vectorMagnetization s β t p (k+1-i) y l
  have hg : Continuous g := ((boundedJets_vectorMagnetization_component s β t (k+1-i) l).1.continuous.comp
    (continuous_const.prodMk continuous_id))
  have hb : ∀y,|g y| ≤ 1 := fun y => vectorMagnetization_component_bound s β t p (k+1-i) y l
  have hh := continuous_vectorStepResponse_variance_field (vectorRecursion s β t p (k+1-i)) g _
    (vectorRecursion_lipschitz s β t p (k+1-i)) hg 1 hb (s.m i)
  have hparam : Continuous (fun z : ℝ×Field n => (((1-t)*β^2*(s.q (i+1)-z.1)),z.2)) := by fun_prop
  have he : (fun z : ℝ×Field n => gradient (vectorFiniteCellPotential s β t p i z.1) z.2 l)=
      (fun z : ℝ×Field n => vectorStepResponse z.1 (s.m i)
        (vectorRecursion s β t p (k+1-i)) g z.2) ∘
        (fun z : ℝ×Field n => (((1-t)*β^2*(s.q (i+1)-z.1)),z.2)) := by
    funext z
    rw [gradient_euclidean_coordinate]
    exact fderiv_vectorColeHopfStep_recursion_coordinate s β t _ _ p _ _ l
  rw [he]
  exact hh.comp hparam

theorem continuous_vectorFiniteCellPotential_hessian_diagonal {n k : ℕ}
    (s : RSBScheme k) (β t : ℝ) (p : Couplings n×ℝ) (i : ℕ) (l : Fin n) :
    Continuous (fun z : ℝ×Field n =>
      directionalHessian (vectorFiniteCellPotential s β t p i z.1) z.2
        (EuclideanSpace.single l (1 : ℝ))) := by
  let f := vectorRecursion s β t p (k+1-i)
  let g := fun y : Field n => vectorMagnetization s β t p (k+1-i) y l
  let H := fun y : Field n => (vectorFieldHessian s β t p (k+1-i) y (EuclideanSpace.single l (1 : ℝ))) l
  have hf := vectorRecursion_lipschitz s β t p (k+1-i)
  have hg : Continuous g := ((boundedJets_vectorMagnetization_component s β t (k+1-i) l).1.continuous.comp
    (continuous_const.prodMk continuous_id))
  have hH : Continuous H := (continuous_vectorFieldHessian_component s β t (k+1-i) l l).comp
    (continuous_const.prodMk continuous_id)
  have hb : ∀y,|g y| ≤ 1 := fun y => vectorMagnetization_component_bound s β t p (k+1-i) y l
  have hHb : ∀y,|H y| ≤ 1 := by
    intro y
    have h := vectorFieldHessian_diagonal_bounds s β t p (k+1-i) y l
    rw [abs_of_nonneg h.1]
    nlinarith [sq_nonneg (g y)]
  have hgb : ∀y,|g y^2| ≤ 1 := by
    intro y
    rw [abs_sq]
    have h := abs_le.mp (hb y)
    nlinarith
  have h₁ := continuous_vectorStepResponse_variance_field f H _ hf hH 1 hHb (s.m i)
  have h₂ := continuous_vectorStepResponse_variance_field f (fun y => g y^2) _ hf (hg.pow 2) 1 hgb (s.m i)
  have h₃ := continuous_vectorStepResponse_variance_field f g _ hf hg 1 hb (s.m i)
  have hh := h₁.add ((continuous_const (y := s.m i)).mul (h₂.sub (h₃.pow 2)))
  have hparam : Continuous (fun z : ℝ×Field n => (((1-t)*β^2*(s.q (i+1)-z.1)),z.2)) := by fun_prop
  have he : (fun z : ℝ×Field n => directionalHessian (vectorFiniteCellPotential s β t p i z.1) z.2
      (EuclideanSpace.single l (1 : ℝ)))=
      (fun z : ℝ×Field n => vectorStepResponse z.1 (s.m i) f H z.2+
        s.m i*(vectorStepResponse z.1 (s.m i) f (fun y => g y^2) z.2-
          (vectorStepResponse z.1 (s.m i) f g z.2)^2)) ∘
        (fun z : ℝ×Field n => (((1-t)*β^2*(s.q (i+1)-z.1)),z.2)) := by
    funext z
    exact directionalHessian_vectorColeHopfStep_recursion_coordinate s β t _ _ p _ _ l
  rw [he]
  exact hh.comp hparam

theorem continuous_vectorFiniteCellTimeField {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (i : ℕ) (hi : i ≤ k+1) :
    Continuous (fun z : ℝ×Field n => vectorFiniteCellTimeField s β t p i z.1 z.2) := by
  apply continuous_const.mul
  apply continuous_finsetSum
  intro l hl
  let G := fun y : Field n => (vectorFieldHessian s β t p (k+1-i) y (EuclideanSpace.single l (1 : ℝ))) l+
    s.m i*(vectorMagnetization s β t p (k+1-i) y l)^2
  have hG : Continuous G := ((continuous_vectorFieldHessian_component s β t (k+1-i) l l).comp
      (continuous_const.prodMk continuous_id)).add
    (continuous_const.mul (((boundedJets_vectorMagnetization_component s β t (k+1-i) l).1.continuous.comp
      (continuous_const.prodMk continuous_id)).pow 2))
  have hb : ∀y,|G y| ≤ 1 := by
    intro y
    have h := vectorRecursion_coordinate_generator_bounds s β t p (k+1-i) (s.m i)
      (s.m_nonneg hi) (s.m_le_one hi) y l
    rw [abs_of_nonneg h.1]
    exact h.2
  have hh := continuous_vectorStepResponse_variance_field (vectorRecursion s β t p (k+1-i)) G _
    (vectorRecursion_lipschitz s β t p (k+1-i)) hG 1 hb (s.m i)
  exact hh.comp (by fun_prop : Continuous (fun z : ℝ×Field n =>
    (((1-t)*β^2*(s.q (i+1)-z.1)),z.2)))

theorem hasDerivAt_vectorFiniteCellPotential_timeField {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (p : Couplings n×ℝ)
    (i : ℕ) (q : ℝ) (hq : q<s.q (i+1)) (x : Field n) :
    HasDerivAt (fun r => vectorFiniteCellPotential s β t p i r x)
      (vectorFiniteCellTimeField s β t p i q x) q :=
  hasDerivAt_vectorFiniteCellPotential_time s β t hβ ht p i q hq x

theorem norm_vectorFiniteCellTimeField_le {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) (i : ℕ) (hi : i ≤ k+1)
    (q : ℝ) (x : Field n) :
    ‖vectorFiniteCellTimeField s β t p i q x‖ ≤ ((1-t)*β^2)*(n : ℝ)/2 := by
  let S := ∑l : Fin n,vectorStepResponse ((1-t)*β^2*(s.q (i+1)-q)) (s.m i)
    (vectorRecursion s β t p (k+1-i))
    (fun y => (vectorFieldHessian s β t p (k+1-i) y (EuclideanSpace.single l (1 : ℝ))) l+
      s.m i*(vectorMagnetization s β t p (k+1-i) y l)^2) x
  have hb (l : Fin n) := vectorStepResponse_recursion_heat_bounds s β t
    ((1-t)*β^2*(s.q (i+1)-q)) (s.m i) p (k+1-i)
    (s.m_nonneg hi) (s.m_le_one hi) x l
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun l _ => (hb l).1
  have hS1 : S ≤ (n : ℝ) := (Finset.sum_le_sum fun l _ => (hb l).2).trans_eq (by simp)
  have hc : 0 ≤ (1-t)*β^2 := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β)
  change ‖-((1-t)*β^2)/2*S‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) hS0)]
  nlinarith

end QuantitativePaper
