module
public import QuantitativePaper.VectorTailTimeBounds

@[expose] public section

/-! Uniform-grid representations of the genuine Gaussian recursion restarted
at an arbitrary overlap. All clamped variances are retained. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

def vectorUniformTailCascade {n : ℕ} (N : ℕ) (c q : ℝ) (a : ℝ→ℝ)
    (f : Field n→ℝ) : ℕ→(Field n→ℝ)
  | 0 => f
  | j+1 => vectorColeHopfStep
      (c*(max q ((N-j : ℕ)/(N : ℝ))-max q ((N-1-j : ℕ)/(N : ℝ))))
      (a ((N-1-j : ℕ)/(N : ℝ))) (vectorUniformTailCascade N c q a f j)

theorem vectorUniformTailCascade_lipschitz {n : ℕ} (N : ℕ) (c q : ℝ)
    (a : ℝ→ℝ) (ha : ∀x,0 ≤ a x) (f : Field n→ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (j : ℕ) :
    LipschitzWith K (vectorUniformTailCascade N c q a f j) := by
  induction j with
  | zero => exact hf
  | succ j ih => exact vectorColeHopfStep_lipschitz _ _ ih _ _ (ha _)

theorem vectorTailRecursion_grid_prefix {n : ℕ} (μ : Paper.ParisiMeasure) (N : ℕ)
    (β t q : ℝ) (p : Couplings n×ℝ) {j : ℕ} (hj : j ≤ N+1) :
    vectorTailRecursion (Paper.parisiGridRSBScheme μ N) β t q p (j+1)=
      vectorUniformTailCascade (N+1) ((1-t)*β^2) q (Paper.parisiCDF μ)
        (vectorTerminalPotential n β t p) j := by
  induction j with
  | zero =>
    funext x
    simp [vectorTailRecursion,Paper.parisiGridRSBScheme,Paper.parisiGridSchemeOverlap,
      vectorUniformTailCascade]
  | succ j ih =>
    rw [vectorTailRecursion,ih (by omega),vectorUniformTailCascade]
    have hi0 : N+2-(j+1)=N+1-j := by omega
    have hi1 : N+3-(j+1)=N+2-j := by omega
    have hm0 : N+1-j ≠ 0 := by omega
    have hq0 : (N+1-j)-1=N-j := by omega
    have hq1 : (N+2-j)-1=N+1-j := by omega
    simp only [hi0,hi1,Paper.parisiGridRSBScheme,Paper.parisiGridSchemeMass,ite_eq_right hm0,
      Paper.parisiGridSchemeOverlap,hq0,hq1,Nat.min_eq_left (by omega : N-j ≤ N+1),
      Nat.min_eq_left (by omega : N+1-j ≤ N+1),parisiCDF_grid_at_node,Nat.add_sub_cancel]
    congr 1
    ring

theorem vectorTailRecursion_grid_eq_uniform {n : ℕ} (μ : Paper.ParisiMeasure) (N : ℕ)
    (β t q : ℝ) (p : Couplings n×ℝ) :
    vectorTailRecursion (Paper.parisiGridRSBScheme μ N) β t q p (N+3)=
      vectorUniformTailCascade (N+1) ((1-t)*β^2) q (Paper.parisiCDF μ)
        (vectorTerminalPotential n β t p) (N+1) := by
  rw [show N+3=(N+2)+1 by omega,vectorTailRecursion]
  simp only [show N+1+2-(N+2)=1 by omega,
    show N+1+1-(N+2)=0 by omega,Paper.parisiGridRSBScheme,
    Paper.parisiGridSchemeOverlap,show 1-1=0 by omega,
    Nat.zero_min,Nat.cast_zero,zero_div,sub_self,mul_zero]
  funext x
  rw [vectorColeHopfStep_zero_variance]
  exact congrFun (vectorTailRecursion_grid_prefix μ N β t q p le_rfl) x

end QuantitativePaper
