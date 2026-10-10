module
public import QuantitativePaper.VectorAlignedProfileStability
public import Paper.ParisiSchemeMeasure
public import Paper.ParisiCDFGrid

@[expose] public section

/-! The finite-profile coefficient bound in the literal CDF L¹ metric.
The measures and their CDFs are the actual atomic scheme measures. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem parisiSchemeCDFDistance_cell {k : ℕ} (s r : RSBScheme k)
    (hq : ∀i,i ≤ k+2 → s.q i=r.q i) {p : ℕ} (hp : p ≤ k+1) :
    (∫t in s.q p..s.q (p+1),
      |Paper.parisiCDF (Paper.parisiSchemeMeasure s) t-
        Paper.parisiCDF (Paper.parisiSchemeMeasure r) t|)=
      (s.q (p+1)-s.q p)*|s.m p-r.m p| := by
  have he : EqOn (fun t => |Paper.parisiCDF (Paper.parisiSchemeMeasure s) t-
      Paper.parisiCDF (Paper.parisiSchemeMeasure r) t|)
      (fun _ => |s.m p-r.m p|) (uIoo (s.q p) (s.q (p+1))) := by
    rw [uIoo_of_le (s.q_mono p hp)]
    intro t ht
    dsimp only
    have htr : t∈Ico (r.q p) (r.q (p+1)) := by
      rw [←hq p (by omega),←hq (p+1) (by omega)]
      exact ⟨ht.1.le,ht.2⟩
    rw [Paper.parisiCDF_scheme_cell s hp ⟨ht.1.le,ht.2⟩,
      Paper.parisiCDF_scheme_cell r hp htr]
  rw [intervalIntegral.integral_congr_uIoo he,intervalIntegral.integral_const]
  simp only [smul_eq_mul]

theorem parisiSchemeCDFDistance_eq_sum {k : ℕ} (s r : RSBScheme k)
    (hq : ∀i,i ≤ k+2 → s.q i=r.q i) :
    Paper.parisiCDFDistance (Paper.parisiSchemeMeasure s) (Paper.parisiSchemeMeasure r)=
      ∑p∈Finset.range (k+2),(s.q (p+1)-s.q p)*|s.m p-r.m p| := by
  have hp := intervalIntegral.sum_integral_adjacent_intervals (a:=s.q) (n:=k+2)
    (fun p _ => Paper.parisiCDF_abs_diff_intervalIntegrable
      (Paper.parisiSchemeMeasure s) (Paper.parisiSchemeMeasure r) (s.q p) (s.q (p+1)))
  rw [s.q_zero,s.q_top] at hp
  rw [Paper.parisiCDFDistance,←hp]
  apply Finset.sum_congr rfl
  intro p hp
  exact parisiSchemeCDFDistance_cell s r hq (by have := Finset.mem_range.mp hp; omega)

theorem vectorAlignedProfileError_eq_CDFDistance {n k : ℕ} (s r : RSBScheme k)
    (β t : ℝ) (hq : ∀i,i ≤ k+2 → s.q i=r.q i) :
    vectorAlignedProfileError (n:=n) s r β t (k+2)=
      (n : ℝ)*((1-t)*β^2)*
        Paper.parisiCDFDistance (Paper.parisiSchemeMeasure s) (Paper.parisiSchemeMeasure r) := by
  rw [parisiSchemeCDFDistance_eq_sum s r hq,Finset.mul_sum]
  unfold vectorAlignedProfileError
  rw [←Finset.sum_range_reflect
    (fun p => (n : ℝ)*((1-t)*β^2)*((s.q (p+1)-s.q p)*|s.m p-r.m p|)) (k+2)]
  apply Finset.sum_congr rfl
  intro l hl
  have hi : k+2-1-l=k+1-l := by omega
  have hs : k+2-l=k+1-l+1 := by have := Finset.mem_range.mp hl; omega
  rw [hi,hs]
  ring

theorem vectorRecursion_aligned_CDFDistance_abs_sub_le {n k : ℕ} (s r : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (hq : ∀i,i ≤ k+2 → s.q i=r.q i)
    (p : Couplings n × ℝ) (x : Field n) :
    |vectorRecursion s β t p (k+2) x-vectorRecursion r β t p (k+2) x| ≤
      (n : ℝ)*((1-t)*β^2)*
        Paper.parisiCDFDistance (Paper.parisiSchemeMeasure s) (Paper.parisiSchemeMeasure r) := by
  simpa only [vectorAlignedProfileError_eq_CDFDistance s r β t hq] using
    vectorRecursion_aligned_profile_abs_sub_le s r β t ht hq p (k+2) x

end QuantitativePaper
