module
public import QuantitativePaper.VectorClampedScheme
public import QuantitativePaper.VectorProfileCDFStability

@[expose] public section

/-! Actual finite tail-profile stability, uniform in the restarted overlap.
The tail is a prefix of a genuine admissible clamped scheme. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem clamped_interval_length_le (q a b : ℝ) (hab : a ≤ b) :
    max q b-max q a ≤ b-a := by
  have hh := max_sub_max_le_max q b q a
  simpa only [sub_self,max_eq_right (sub_nonneg.mpr hab)] using hh

theorem vectorTailRecursion_aligned_profile_abs_sub_le {n k : ℕ} (s r : RSBScheme k)
    (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1)
    (hgrid : ∀i,i ≤ k+2 → s.q i=r.q i) (p : Couplings n×ℝ) (x : Field n) :
    |vectorTailRecursion s β t q p (k+2) x-vectorTailRecursion r β t q p (k+2) x| ≤
      vectorAlignedProfileError (n:=n) s r β t (k+2) := by
  have hclamp : ∀i,i ≤ k+1+2 →
      (vectorClampedScheme s q hq).q i=(vectorClampedScheme r q hq).q i := by
    intro i hi
    by_cases h0 : i=0
    · subst i;simp [vectorClampedScheme,clampedSchemeOverlap]
    · simp only [vectorClampedScheme,clampedSchemeOverlap,ite_eq_right h0]
      rw [hgrid (i-1) (by omega)]
  have hh := vectorRecursion_aligned_profile_abs_sub_le
    (vectorClampedScheme s q hq) (vectorClampedScheme r q hq) β t ht hclamp p (k+2) x
  rw [←vectorTailRecursion_eq_clamped s β t q hq p le_rfl,
    ←vectorTailRecursion_eq_clamped r β t q hq p le_rfl] at hh
  apply hh.trans
  unfold vectorAlignedProfileError
  apply Finset.sum_le_sum
  intro l hl
  have hl' : l<k+2 := Finset.mem_range.mp hl
  have hi0 : k+1+1-l=(k+1-l)+1 := by omega
  have hi1 : k+1+2-l=(k+2-l)+1 := by omega
  rw [hi0,hi1,vectorClampedScheme_mass_succ,vectorClampedScheme_mass_succ,
    vectorClampedScheme_overlap_succ,vectorClampedScheme_overlap_succ]
  simp only [show k+1-l+1=k+2-l by omega]
  have hlength := clamped_interval_length_le q (s.q (k+1-l)) (s.q (k+2-l))
    (s.q_mono' (k+2-l) (by omega) (k+1-l) (by omega))
  have hc : 0 ≤ (n : ℝ)*((1-t)*β^2) :=
    mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β))
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength hc)
    (abs_nonneg (s.m (k+1-l)-r.m (k+1-l)))
  convert hb using 1 <;> ring

theorem vectorTailRecursion_aligned_CDFDistance_abs_sub_le {n k : ℕ} (s r : RSBScheme k)
    (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1)
    (hgrid : ∀i,i ≤ k+2 → s.q i=r.q i) (p : Couplings n×ℝ) (x : Field n) :
    |vectorTailRecursion s β t q p (k+2) x-vectorTailRecursion r β t q p (k+2) x| ≤
      (n : ℝ)*((1-t)*β^2)*Paper.parisiCDFDistance (Paper.parisiSchemeMeasure s) (Paper.parisiSchemeMeasure r) := by
  simpa only [vectorAlignedProfileError_eq_CDFDistance s r β t hgrid] using
    vectorTailRecursion_aligned_profile_abs_sub_le s r β t q ht hq hgrid p x

end QuantitativePaper
