module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! The exact root-localization smoothing width, including zero free
mass. Its budget and inverse-width estimates are derived algebraically. -/
noncomputable section
open Set
namespace QuantitativeFollowup

def rootSmoothingWidth (q eta rho m : ℝ) : ℝ :=
  if m=0 then q/8 else min (q/8) (Real.sqrt (eta/(rho*m)))

theorem rootSmoothingWidth_pos_le (q eta rho m : ℝ) (hq : 0 < q)
    (heta : 0 < eta) (hrho : 0 < rho) (hm : 0 ≤ m) :
    0 < rootSmoothingWidth q eta rho m ∧ rootSmoothingWidth q eta rho m ≤ q/8 := by
  unfold rootSmoothingWidth
  split_ifs with hm0
  · exact ⟨by positivity,le_rfl⟩
  · have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    exact ⟨lt_min (by positivity) (Real.sqrt_pos.mpr (div_pos heta (mul_pos hrho hmp))),min_le_left _ _⟩

theorem rootSmoothingWidth_mem (q eta rho m : ℝ) (hq : q ∈ Ioc (0 : ℝ) (1/4))
    (heta : 0 < eta) (hrho : 0 < rho) (hm : 0 ≤ m) :
    rootSmoothingWidth q eta rho m ∈ Ioc (0 : ℝ) (1-q) := by
  have hh := rootSmoothingWidth_pos_le q eta rho m hq.1 heta hrho hm
  exact ⟨hh.1,by linarith [hq.2,hh.2]⟩

theorem rootSmoothingWidth_budget (q eta rho m : ℝ) (hq : 0 < q)
    (heta : 0 < eta) (hrho : 0 < rho) (hm : 0 ≤ m) :
    rho*m*(rootSmoothingWidth q eta rho m)^2 ≤ eta := by
  by_cases hm0 : m=0
  · simp only [hm0,mul_zero,zero_mul]
    exact heta.le
  · have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    have hh := rootSmoothingWidth_pos_le q eta rho m hq heta hrho hm
    have hs : rootSmoothingWidth q eta rho m ≤ Real.sqrt (eta/(rho*m)) := by
      unfold rootSmoothingWidth
      rw [ite_eq_right hm0]
      exact min_le_right _ _
    have hsq := pow_le_pow_left₀ hh.1.le hs 2
    rw [Real.sq_sqrt (div_nonneg heta.le (mul_nonneg hrho.le hm))] at hsq
    have hc := mul_le_mul_of_nonneg_left hsq (mul_nonneg hrho.le hm)
    have he : (rho*m)*(eta/(rho*m))=eta := by field_simp
    rwa [he] at hc

theorem rootSmoothingWidth_inverse_bound (q eta rho m : ℝ) (hq : 0 < q)
    (_heta : 0 < eta) (_hrho : 0 < rho) (hm : 0 ≤ m) :
    m/rootSmoothingWidth q eta rho m ≤ 8*m/q+m*Real.sqrt (rho*m/eta) := by
  by_cases hm0 : m=0
  · simp [hm0]
  · by_cases hqsmall : q/8 ≤ Real.sqrt (eta/(rho*m))
    · unfold rootSmoothingWidth
      rw [ite_eq_right hm0,min_eq_left hqsmall]
      have he : m/(q/8)=8*m/q := by field_simp
      rw [he]
      exact le_add_of_nonneg_right (mul_nonneg hm (Real.sqrt_nonneg _))
    · unfold rootSmoothingWidth
      rw [ite_eq_right hm0,min_eq_right (le_of_not_ge hqsmall)]
      have he : m/Real.sqrt (eta/(rho*m))=m*Real.sqrt (rho*m/eta) := by
        rw [div_eq_mul_inv,←Real.sqrt_inv,inv_div]
      rw [he]
      exact le_add_of_nonneg_left (div_nonneg (mul_nonneg (by norm_num) hm) hq.le)

end QuantitativeFollowup
