module
public import QuantitativeFollowup.DirectionalCovarianceDecay

@[expose] public section

/-! Actual dyadic overlap nodes approaching the right endpoint, including
the degenerate interval. -/
noncomputable section
open Set
open scoped BigOperators
namespace QuantitativeFollowup

def dyadicOverlap (p q : Paper.Overlap) (hpq : p≤q) (k : ℕ) : Paper.Overlap :=
  ⟨(q:ℝ)-((q:ℝ)-p)*(1/2:ℝ)^k,by
    have hpow : (1/2:ℝ)^k≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hpos : 0≤(1/2:ℝ)^k := pow_nonneg (by norm_num) _
    have hd : 0≤(q:ℝ)-p := sub_nonneg.mpr hpq
    have hprod := mul_le_mul_of_nonneg_left hpow hd
    have hnon := mul_nonneg hd hpos
    constructor <;> nlinarith [p.property.1,q.property.2]⟩

theorem dyadicOverlap_zero (p q : Paper.Overlap) (hpq : p≤q) : dyadicOverlap p q hpq 0=p := by
  apply Subtype.ext
  simp [dyadicOverlap]

theorem dyadicOverlap_one (p q : Paper.Overlap) (hpq : p≤q) :
    (dyadicOverlap p q hpq 1:ℝ)=((p:ℝ)+q)/2 := by
  dsimp [dyadicOverlap]
  ring

theorem monotone_dyadicOverlap (p q : Paper.Overlap) (hpq : p≤q) :
    Monotone (dyadicOverlap p q hpq) := by
  apply monotone_nat_of_le_succ
  intro k
  change (q:ℝ)-((q:ℝ)-p)*(1/2:ℝ)^k≤(q:ℝ)-((q:ℝ)-p)*(1/2:ℝ)^(k+1)
  rw [pow_succ]
  have h := mul_nonneg (sub_nonneg.mpr (show (p:ℝ)≤q from hpq)) (pow_nonneg (by norm_num : (0:ℝ)≤1/2) k)
  nlinarith

theorem dyadicOverlap_le (p q : Paper.Overlap) (hpq : p≤q) (k : ℕ) : dyadicOverlap p q hpq k≤q := by
  change (q:ℝ)-((q:ℝ)-p)*(1/2:ℝ)^k≤q
  exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr hpq) (pow_nonneg (by norm_num) _))

theorem dyadicOverlap_lt (p q : Paper.Overlap) (hpq : p<q) (k : ℕ) : dyadicOverlap p q hpq.le k<q := by
  change (q:ℝ)-((q:ℝ)-p)*(1/2:ℝ)^k<q
  exact sub_lt_self _ (mul_pos (sub_pos.mpr hpq) (pow_pos (by norm_num) _))

theorem dyadicOverlap_gap (p q : Paper.Overlap) (hpq : p≤q) (k : ℕ) :
    (q:ℝ)-dyadicOverlap p q hpq k=((q:ℝ)-p)*(1/2:ℝ)^k := by
  dsimp [dyadicOverlap]
  ring

theorem dyadicOverlap_gap_double (p q : Paper.Overlap) (hpq : p≤q) (k : ℕ) :
    (q:ℝ)-dyadicOverlap p q hpq k=2*((q:ℝ)-dyadicOverlap p q hpq (k+1)) := by
  rw [dyadicOverlap_gap,dyadicOverlap_gap,pow_succ]
  ring

theorem dyadicOverlap_middle_le (p q : Paper.Overlap) (hpq : p≤q) (k : ℕ) :
    dyadicOverlap p q hpq 1≤dyadicOverlap p q hpq (k+1) :=
  monotone_dyadicOverlap p q hpq (by omega)

theorem dyadicOverlap_increment_sum {E : Type*} [AddCommGroup E]
    (f : ℕ→E) (K : ℕ) : (∑i : Fin K,(f (i.val+1)-f i.val))=f K-f 0 := by
  calc
    _ = ∑i∈Finset.range K,(f (i+1)-f i) :=
      Fin.sum_univ_eq_sum_range (fun i=>f (i+1)-f i) K
    _ = _ := Finset.sum_range_sub f K

end QuantitativeFollowup
