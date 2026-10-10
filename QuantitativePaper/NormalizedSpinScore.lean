module
public import QuantitativePaper.VectorOverlapScore

@[expose] public section

/-! The literal normalized spin/mean score, with its dimension-free bound.
These are finite-spin statements, independent of posterior estimates. -/
noncomputable section
open Set
open scoped BigOperators
namespace QuantitativePaper
variable {n : ℕ}

def normalizedSpinScore (m : Field n) (σ : Configuration n) : ℝ :=
  (fieldDot m σ-‖m‖^2/2)/(n : ℝ)

theorem continuous_normalizedSpinScore (σ : Configuration n) :
    Continuous (fun m : Field n=>normalizedSpinScore m σ) := by
  unfold normalizedSpinScore fieldDot
  fun_prop

theorem norm_sq_le_dimension_of_components (m : Field n)
    (hm : ∀i,|m i|≤1) : ‖m‖^2≤(n : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _≤∑_i : Fin n,(1 : ℝ) := Finset.sum_le_sum fun i _=>by
      have hh:=abs_le.mp (hm i)
      nlinarith
    _=(n : ℝ) := by simp

theorem normalizedSpinScore_bound (m : Field n) (σ : Configuration n)
    (hm : ∀i,|m i|≤1) : |normalizedSpinScore m σ|≤3/2 := by
  have hd : |fieldDot m σ|≤(n : ℝ) := by
    unfold fieldDot
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _≤∑_i : Fin n,(1 : ℝ) := Finset.sum_le_sum fun i _=>by
        rw [abs_mul,Paper.abs_spinSign,mul_one]
        exact hm i
      _=(n : ℝ) := by simp
  have hs:=norm_sq_le_dimension_of_components m hm
  by_cases hn : n=0
  · subst n
    norm_num [normalizedSpinScore]
  · have hnR : 0<(n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [normalizedSpinScore,abs_div,abs_of_pos hnR]
    apply (div_le_iff₀ hnR).mpr
    have hh := abs_sub (fieldDot m σ) (‖m‖^2/2)
    rw [abs_of_nonneg (by positivity : 0≤‖m‖^2/2)] at hh
    nlinarith

theorem vectorEuclideanOverlapScore_eq_normalized {k : ℕ}
    (s : SpinGlass.Targets.RSBScheme k) (β t : ℝ) (σ : Configuration n)
    (i : ℕ) (z : VectorGaussianSpace n k) :
    vectorEuclideanOverlapScore s β t σ i z=
      normalizedSpinScore (vectorEuclideanMagnetization s β t i z) σ := rfl

end QuantitativePaper
