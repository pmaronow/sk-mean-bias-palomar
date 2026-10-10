module
public import QuantitativePaper.VectorFiniteCellBounds
public import QuantitativePaper.VectorVarianceContinuity

@[expose] public section

/-! Closed-cell time comparison, including the zero-variance right endpoint.
The argument combines actual Gaussian continuity with the interior PDE bound;
it never assumes a time derivative at zero variance. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem continuous_vectorFiniteCellPotential_time {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (i : ℕ) (x : Field n) :
    Continuous (fun q => vectorFiniteCellPotential s β t p i q x) := by
  exact (continuous_vectorColeHopfStep_variance _ _ (vectorRecursion_lipschitz s β t p (k+1-i))
    (s.m i) x).comp (by fun_prop)

theorem antitoneOn_vectorFiniteCellPotential_time {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (p : Couplings n × ℝ)
    (i : ℕ) (hi : i ≤ k+1) (x : Field n) :
    AntitoneOn (fun q => vectorFiniteCellPotential s β t p i q x) (Iic (s.q (i+1))) := by
  apply antitoneOn_of_deriv_nonpos (convex_Iic _) (continuous_vectorFiniteCellPotential_time s β t p i x).continuousOn
  · intro q hq
    rw [interior_Iic] at hq
    exact (hasDerivAt_vectorFiniteCellPotential_time s β t hβ ht p i q hq x).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Iic] at hq
    exact (vectorFiniteCellPotential_time_deriv_bounds s β t hβ ht p i hi q hq x).2

theorem vectorFiniteCellPotential_time_sub_bounds {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (p : Couplings n × ℝ)
    (i : ℕ) (hi : i ≤ k+1) (r q : ℝ) (hrq : r ≤ q) (hq : q ≤ s.q (i+1)) (x : Field n) :
    0 ≤ vectorFiniteCellPotential s β t p i r x-vectorFiniteCellPotential s β t p i q x ∧
    vectorFiniteCellPotential s β t p i r x-vectorFiniteCellPotential s β t p i q x ≤
      ((1-t)*β^2)*(n : ℝ)/2*(q-r) := by
  have hf := continuous_vectorFiniteCellPotential_time s β t p i x
  have ha := antitoneOn_vectorFiniteCellPotential_time s β t hβ ht p i hi x
  refine ⟨sub_nonneg.mpr (ha (hrq.trans hq) hq hrq),?_⟩
  have hh := (convex_Iic (s.q (i+1))).image_sub_le_mul_sub_of_deriv_le
    hf.neg.continuousOn
    (fun u hu => by
      rw [interior_Iic] at hu
      exact (hasDerivAt_vectorFiniteCellPotential_time s β t hβ ht p i u hu x).neg.differentiableAt.differentiableWithinAt)
    (C := ((1-t)*β^2)*(n : ℝ)/2)
    (fun u hu => by
      rw [interior_Iic] at hu
      change deriv (fun q => -vectorFiniteCellPotential s β t p i q x) u ≤ _
      have hd := hasDerivAt_vectorFiniteCellPotential_time s β t hβ ht p i u hu x
      have hn : deriv (fun q => -vectorFiniteCellPotential s β t p i q x) u=
          -deriv (fun q => vectorFiniteCellPotential s β t p i q x) u := by
        convert! hd.neg.deriv using 1
        exact hd.deriv.symm ▸ rfl
      rw [hn]
      have hb := (vectorFiniteCellPotential_time_deriv_bounds s β t hβ ht p i hi u hu x).1
      linarith)
    r (hrq.trans hq) q hq hrq
  simpa only [Pi.neg_apply,neg_sub_neg] using hh

theorem vectorFiniteCellPotential_time_abs_sub_le {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (p : Couplings n × ℝ)
    (i : ℕ) (hi : i ≤ k+1) (r q : ℝ) (hrq : r ≤ q) (hq : q ≤ s.q (i+1)) (x : Field n) :
    |vectorFiniteCellPotential s β t p i r x-vectorFiniteCellPotential s β t p i q x| ≤
      ((1-t)*β^2)*(n : ℝ)/2*(q-r) := by
  have hb := vectorFiniteCellPotential_time_sub_bounds s β t hβ ht p i hi r q hrq hq x
  rw [abs_of_nonneg hb.1]
  exact hb.2

end QuantitativePaper
