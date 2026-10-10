module
public import QuantitativePaper.VectorFiniteCellComparison

@[expose] public section

/-! A depth-independent variance Lipschitz bound for an actual vector
recursion terminal. Zero variance uses genuine continuity rather than a
globally two-sided derivative. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem vectorColeHopfStep_recursion_variance_deriv_bounds {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (j : ℕ) (m : ℝ) (hm : m∈Icc (0 : ℝ) 1)
    (x : Field n) {v : ℝ} (hv : 0<v) :
    0 ≤ deriv (fun u => vectorColeHopfStep u m (vectorRecursion s β t p j) x) v ∧
    deriv (fun u => vectorColeHopfStep u m (vectorRecursion s β t p j) x) v ≤ (n : ℝ)/2 := by
  rw [(hasDerivAt_vectorColeHopfStep_variance s β t p j m x hv).deriv]
  have hb (i : Fin n) := vectorStepResponse_recursion_heat_bounds s β t v m p j hm.1 hm.2 x i
  refine ⟨div_nonneg (Finset.sum_nonneg (fun i _ => (hb i).1)) (by norm_num),?_⟩
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑i : Fin n,(1 : ℝ) := Finset.sum_le_sum (fun i _ => (hb i).2)
    _ = (n : ℝ) := by simp

theorem monotoneOn_vectorColeHopfStep_recursion_variance {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (j : ℕ) (m : ℝ) (hm : m∈Icc (0 : ℝ) 1) (x : Field n) :
    MonotoneOn (fun v => vectorColeHopfStep v m (vectorRecursion s β t p j) x) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    (continuous_vectorColeHopfStep_variance _ _ (vectorRecursion_lipschitz s β t p j) m x).continuousOn
  · intro v hv
    rw [interior_Ici] at hv
    exact (hasDerivAt_vectorColeHopfStep_variance s β t p j m x hv).differentiableAt.differentiableWithinAt
  · intro v hv
    rw [interior_Ici] at hv
    exact (vectorColeHopfStep_recursion_variance_deriv_bounds s β t p j m hm x hv).1

theorem vectorColeHopfStep_recursion_variance_sub_bounds {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (j : ℕ) (m : ℝ) (hm : m∈Icc (0 : ℝ) 1)
    (v w : ℝ) (hv : 0 ≤ v) (hvw : v ≤ w) (x : Field n) :
    0 ≤ vectorColeHopfStep w m (vectorRecursion s β t p j) x-
        vectorColeHopfStep v m (vectorRecursion s β t p j) x ∧
    vectorColeHopfStep w m (vectorRecursion s β t p j) x-
        vectorColeHopfStep v m (vectorRecursion s β t p j) x ≤ (n : ℝ)/2*(w-v) := by
  have hcont := continuous_vectorColeHopfStep_variance _ _ (vectorRecursion_lipschitz s β t p j) m x
  refine ⟨sub_nonneg.mpr (monotoneOn_vectorColeHopfStep_recursion_variance s β t p j m hm x
    hv (hv.trans hvw) hvw),?_⟩
  exact (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le hcont.continuousOn
    (fun u hu => by
      rw [interior_Ici] at hu
      exact (hasDerivAt_vectorColeHopfStep_variance s β t p j m x hu).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [interior_Ici] at hu
      exact (vectorColeHopfStep_recursion_variance_deriv_bounds s β t p j m hm x hu).2)
    v hv w (hv.trans hvw) hvw

theorem vectorColeHopfStep_recursion_variance_abs_sub_le {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (j : ℕ) (m : ℝ) (hm : m∈Icc (0 : ℝ) 1)
    (v w : ℝ) (hv : 0 ≤ v) (hw : 0 ≤ w) (x : Field n) :
    |vectorColeHopfStep w m (vectorRecursion s β t p j) x-
      vectorColeHopfStep v m (vectorRecursion s β t p j) x| ≤ (n : ℝ)/2*|w-v| := by
  rcases le_total v w with h|h
  · have hh := vectorColeHopfStep_recursion_variance_sub_bounds s β t p j m hm v w hv h x
    rw [abs_of_nonneg hh.1,abs_of_nonneg (sub_nonneg.mpr h)]
    exact hh.2
  · rw [abs_sub_comm,abs_sub_comm w v]
    have hh := vectorColeHopfStep_recursion_variance_sub_bounds s β t p j m hm w v hw h x
    rw [abs_of_nonneg hh.1,abs_of_nonneg (sub_nonneg.mpr h)]
    exact hh.2

end QuantitativePaper
