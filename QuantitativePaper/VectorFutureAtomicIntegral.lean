module
public import QuantitativePaper.VectorFutureCovarianceKernels
public import FRSB.FiniteForwardAction
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! Exact conversion of the finite depth-indexed CDF-jump sum into the
future part of the actual atomic profile measure, keeping repeated endpoints. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1400000
variable {k : ℕ}

theorem vectorDepthFutureSum_eq_Ico (s : RSBScheme k) (i : ℕ) (hi : i ≤ k+1)
    (f : ℝ → ℝ) :
    (∑u ∈ Finset.range (k+2-i),
      (observableDepthMass s u - observableDepthMass s (u+1))*f (s.q (k+2-u))) =
      ∑v ∈ Finset.Ico i (k+1), (s.m (v+1)-s.m v)*f (s.q (v+1)) := by
  let h := fun v => (s.m (v+1)-s.m v)*f (s.q (v+1))
  have hj : k+2-i=(k+1-i)+1 := by omega
  rw [hj, Finset.sum_range_succ']
  have hzero : (observableDepthMass s 0-observableDepthMass s (0+1))*f (s.q (k+2-0))=0 := by
    simp [observableDepthMass, s.m_top]
  rw [hzero, add_zero]
  have he : (∑u ∈ Finset.range (k+1-i),
      (observableDepthMass s (u+1)-observableDepthMass s (u+1+1))*f (s.q (k+2-(u+1)))) =
      ∑u ∈ Finset.range (k+1-i), h (k-u) := by
    apply Finset.sum_congr rfl
    intro u hu
    have hule : u ≤ k := by have := Finset.mem_range.mp hu; omega
    have h1 : k+1-u=k-u+1 := by omega
    have h2 : k+1-(u+1)=k-u := by omega
    have h3 : k+2-(u+1)=k-u+1 := by omega
    simp only [observableDepthMass_succ, h1, h2, h3, h]
  rw [he]
  have href := Finset.sum_Ico_reflect h 0 (n:=k) (m:=k+1-i) (Nat.sub_le (k+1) i)
  have hcancel : k+1-(k+1-i)=i := by omega
  simpa only [Nat.Ico_zero_eq_range, Nat.sub_zero, hcancel, h] using href

theorem vectorDepthFutureSum_eq_profileIntegral (s : RSBScheme k) (i : ℕ) (hi : i ≤ k+1)
    (horder : ∀p : Fin (k+1), s.q i < s.q (p+1) ↔ i < (p:ℕ)+1) (f : ℝ → ℝ) :
    (∑u ∈ Finset.range (k+2-i),
      (observableDepthMass s u - observableDepthMass s (u+1))*f (s.q (k+2-u))) =
      ∫q : Paper.Overlap, if s.q i < (q:ℝ) then f q else 0
        ∂(Paper.parisiSchemeMeasure s : Measure Paper.Overlap) := by
  rw [vectorDepthFutureSum_eq_Ico s i hi f, FRSB.integral_parisiSchemeMeasure]
  let h := fun v => (s.m (v+1)-s.m v)*f (s.q (v+1))
  have he : (∑p : Fin (k+1), (s.m (p+1)-s.m p)*
      (if s.q i < (Paper.parisiSchemeAtom s p:ℝ) then f (Paper.parisiSchemeAtom s p) else 0)) =
      ∑p : Fin (k+1), if i ≤ (p:ℕ) then h p else 0 := by
    apply Finset.sum_congr rfl
    intro p _
    change (s.m (p+1)-s.m p)*(if s.q i < s.q (p+1) then f (s.q (p+1)) else 0) = _
    simp only [horder p, Nat.lt_add_one_iff, mul_ite, mul_zero, h]
  rw [he]
  change (∑v ∈ Finset.Ico i (k+1), h v) =
    ∑p : Fin (k+1), (fun v : ℕ => if i ≤ v then h v else 0) p
  rw [Fin.sum_univ_eq_sum_range (fun v : ℕ => if i ≤ v then h v else 0)]
  change (∑v ∈ Finset.Ico i (k+1), h v) = ∑v ∈ Finset.range (k+1), if i ≤ v then h v else 0
  rw [←Finset.sum_filter]
  congr 1
  ext v
  simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range, and_comm]

end QuantitativePaper
