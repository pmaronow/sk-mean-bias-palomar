module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! The exact five-fourths optimization used in the short-variance mean
bound. This deterministic calculus is later applied to the actual finite
SK normalized cumulant function and the genuine scalar trial cost. -/
noncomputable section
namespace QuantitativePaper
set_option maxHeartbeats 600000

theorem short_variance_mean_optimization (C L : ℝ) (hC : 0≤C) (hL : 0<L) :
    ∃c : ℝ,0<c ∧ ∀M v : ℝ,0<v→v≤1→
      (∀lam : ℝ,0<lam→lam≤L→v*lam/2-C*lam^5≤M)→c*v^(5/4:ℝ)≤M:=by
  let a:=min L (min 1 (1/(4*(C+1))))
  have ha : 0<a:=lt_min hL (lt_min (by norm_num) (by positivity))
  have haL : a≤L:=min_le_left _ _
  have ha1 : a≤1:=(min_le_right _ _).trans (min_le_left _ _)
  have haC : a≤1/(4*(C+1)):=(min_le_right _ _).trans (min_le_right _ _)
  have hprod : 4*(C+1)*a≤1:=by
    have hp : 0<4*(C+1):=by positivity
    have hh:=(le_div_iff₀ hp).mp haC
    nlinarith
  have ha4 : a^4≤a:=by
    have hs : a^2≤a:=by nlinarith
    have ht : (a^2)^2≤a^2:=by nlinarith [sq_nonneg (a-1)]
    nlinarith [sq_nonneg a]
  have hCa : C*a^4≤1/4:=by
    have hh:=mul_le_mul_of_nonneg_left ha4 hC
    nlinarith
  refine ⟨a/4,by positivity,?_⟩
  intro M v hv hv1 hM
  let z:=v^(1/4:ℝ)
  have hz : 0<z:=Real.rpow_pos_of_pos hv _
  have hz1 : z≤1:=Real.rpow_le_one hv.le hv1 (by norm_num)
  have hz4 : z^4=v:=by
    rw [←Real.rpow_mul_natCast hv.le (1/4:ℝ) 4]
    norm_num
  have hv5 : v^(5/4:ℝ)=v*z:=by
    rw [show (5/4:ℝ)=1+1/4 by norm_num,Real.rpow_add hv]
    simp only [Real.rpow_one,z]
  have hlam : a*z≤L:=(mul_le_mul_of_nonneg_left hz1 ha.le).trans (by simpa using haL)
  have hm:=hM (a*z) (mul_pos ha hz) hlam
  have he : C*(a*z)^5≤v*(a*z)/4:=by
    calc
      C*(a*z)^5=(C*a^4)*(v*z)*a:=by rw [←hz4];ring
      _≤(1/4)*(v*z)*a:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCa (by positivity)) ha.le
      _=v*(a*z)/4:=by ring
  rw [hv5]
  nlinarith

end QuantitativePaper
