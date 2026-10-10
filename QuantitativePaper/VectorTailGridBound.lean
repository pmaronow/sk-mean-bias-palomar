module
public import QuantitativePaper.VectorTailRefinement
public import QuantitativePaper.VectorTailProfileStability
public import QuantitativePaper.VectorGridCDFBound

@[expose] public section

/-! Actual profile estimates for restarted grid recursions, uniform over
all physical restart overlaps. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

theorem vectorTailRecursion_grid_profile_abs_sub_le {n : ℕ} (μ ν : Paper.ParisiMeasure)
    (N : ℕ) (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) :
    |vectorTailRecursion (Paper.parisiGridRSBScheme μ N) β t q p (N+3) x-
      vectorTailRecursion (Paper.parisiGridRSBScheme ν N) β t q p (N+3) x| ≤
      (n : ℝ)*((1-t)*β^2)*(Paper.parisiCDFDistance μ ν+2/(N+1 : ℕ)) := by
  have hc : 0 ≤ (n : ℝ)*((1-t)*β^2) :=
    mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β))
  have hh := vectorTailRecursion_aligned_CDFDistance_abs_sub_le
    (Paper.parisiGridRSBScheme μ N) (Paper.parisiGridRSBScheme ν N) β t q ht hq
    (fun _ _ => rfl) p x
  rw [FRSB.parisiSchemeMeasure_grid_eq,FRSB.parisiSchemeMeasure_grid_eq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (parisiCDFDistance_grid_pair_le μ ν N) hc)

theorem vectorTailRecursion_grid_adjacent_abs_sub_le {n : ℕ} (μ : Paper.ParisiMeasure)
    (N : ℕ) (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) :
    |vectorTailRecursion (Paper.parisiGridRSBScheme μ (2*N+1)) β t q p (2*N+4) x-
      vectorTailRecursion (Paper.parisiGridRSBScheme μ N) β t q p (N+3) x| ≤
      2*(n : ℝ)*((1-t)*β^2)/(N+1 : ℕ) := by
  have hc : 0 ≤ (n : ℝ)*((1-t)*β^2) :=
    mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β))
  have hh := vectorTailRecursion_grid_profile_abs_sub_le μ (Paper.parisiGridMeasure μ N)
    (2*N+1) β t q ht hq p x
  rw [vectorTailRecursion_grid_refine_coarse μ N β t q ht p] at hh
  have he : (n : ℝ)*((1-t)*β^2)*(1/(N+1 : ℕ)+2/(2*N+1+1 : ℕ))=
      2*(n : ℝ)*((1-t)*β^2)/(N+1 : ℕ) := by
    push_cast
    field_simp
    ring
  exact hh.trans (he ▸ mul_le_mul_of_nonneg_left
    (add_le_add (Paper.parisiCDFDistance_grid_le μ N) le_rfl) hc)

end QuantitativePaper
