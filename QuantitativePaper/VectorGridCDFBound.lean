module
public import QuantitativePaper.VectorProfileCDFStability
public import FRSB.GridMeasureIdentification

@[expose] public section

/-! Actual CDF-L¹ estimates for uniform-grid probability laws. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

theorem parisiCDFDistance_triangle (μ ν ρ : Paper.ParisiMeasure) :
    Paper.parisiCDFDistance μ ρ ≤ Paper.parisiCDFDistance μ ν+Paper.parisiCDFDistance ν ρ := by
  unfold Paper.parisiCDFDistance
  rw [←intervalIntegral.integral_add (Paper.parisiCDF_abs_diff_intervalIntegrable μ ν 0 1)
    (Paper.parisiCDF_abs_diff_intervalIntegrable ν ρ 0 1)]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (Paper.parisiCDF_abs_diff_intervalIntegrable μ ρ 0 1)
    ((Paper.parisiCDF_abs_diff_intervalIntegrable μ ν 0 1).add
      (Paper.parisiCDF_abs_diff_intervalIntegrable ν ρ 0 1))
  intro t ht
  exact abs_sub_le _ _ _

theorem parisiCDFDistance_grid_pair_le (μ ν : Paper.ParisiMeasure) (N : ℕ) :
    Paper.parisiCDFDistance (Paper.parisiGridMeasure μ N) (Paper.parisiGridMeasure ν N) ≤
      Paper.parisiCDFDistance μ ν+2/(N+1 : ℕ) := by
  have h1 := parisiCDFDistance_triangle (Paper.parisiGridMeasure μ N) μ (Paper.parisiGridMeasure ν N)
  have h2 := parisiCDFDistance_triangle μ ν (Paper.parisiGridMeasure ν N)
  have he : Paper.parisiCDFDistance (Paper.parisiGridMeasure μ N) μ=
      Paper.parisiCDFDistance μ (Paper.parisiGridMeasure μ N) := by
    unfold Paper.parisiCDFDistance
    apply intervalIntegral.integral_congr
    intro t ht
    exact abs_sub_comm _ _
  rw [he] at h1
  have hm := Paper.parisiCDFDistance_grid_le μ N
  have hn := Paper.parisiCDFDistance_grid_le ν N
  simp only [div_eq_mul_inv,one_mul] at hm hn ⊢
  linarith

theorem vectorRecursion_grid_profile_abs_sub_le {n : ℕ} (μ ν : Paper.ParisiMeasure)
    (N : ℕ) (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) (x : Field n) :
    |vectorRecursion (Paper.parisiGridRSBScheme μ N) β t p (N+3) x-
      vectorRecursion (Paper.parisiGridRSBScheme ν N) β t p (N+3) x| ≤
      (n : ℝ)*((1-t)*β^2)*
        (Paper.parisiCDFDistance μ ν+2/(N+1 : ℕ)) := by
  have hc : 0 ≤ (n : ℝ)*((1-t)*β^2) :=
    mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β))
  have hh := vectorRecursion_aligned_CDFDistance_abs_sub_le
    (Paper.parisiGridRSBScheme μ N) (Paper.parisiGridRSBScheme ν N) β t ht (fun _ _ => rfl) p x
  rw [FRSB.parisiSchemeMeasure_grid_eq,FRSB.parisiSchemeMeasure_grid_eq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (parisiCDFDistance_grid_pair_le μ ν N) hc)

end QuantitativePaper
