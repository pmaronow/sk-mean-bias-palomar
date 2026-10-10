module
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section

/-! The exact integer choice and constant 56 in the dyadic covariance bound. -/
noncomputable section
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

def logPlus (z : ℝ) : ℝ := max (Real.log z) 0
def covarianceDyadicCount (z : ℝ) : ℕ := Nat.ceil (Real.logb 2 (2+z))

theorem logPlus_nonneg (z : ℝ) : 0≤logPlus z := le_max_right _ _

theorem covarianceDyadicCount_pos {z : ℝ} (hz : 0≤z) : 1≤covarianceDyadicCount z := by
  exact Nat.one_le_ceil_iff.mpr (Real.logb_pos (by norm_num) (by linarith : (1:ℝ)<2+z))

theorem covarianceDyadicCount_power {z : ℝ} (hz : 0≤z) : 2+z≤(2:ℝ)^covarianceDyadicCount z := by
  have hh := (Real.logb_le_iff_le_rpow (b:=2) (by norm_num) (by linarith : (0:ℝ)<2+z)).mp
    (Nat.le_ceil (Real.logb 2 (2+z)))
  simpa only [covarianceDyadicCount,Real.rpow_natCast] using hh

theorem covarianceDyadicCount_log_bound {z : ℝ} (hz : 0≤z) :
    (covarianceDyadicCount z:ℝ)<3+2*logPlus z := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : (1/2:ℝ)<Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog3 : Real.log 3<2*Real.log 2 := by
    have hh := Real.log_lt_log (by norm_num : (0:ℝ)<3) (by norm_num : (3:ℝ)<4)
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hh
    simpa only [Nat.cast_ofNat] using hh
  have hmax : Real.log (max (1:ℝ) z)=logPlus z := by
    by_cases hz1 : z≤1
    · rw [max_eq_left hz1,Real.log_one]
      exact (max_eq_right (Real.log_nonpos hz hz1)).symm
    · have hz1' : 1≤z := le_of_not_ge hz1
      rw [max_eq_right hz1']
      exact (max_eq_left (Real.log_nonneg hz1')).symm
  have hzmax : 2+z≤3*max (1:ℝ) z := by
    have h1 := le_max_left (1:ℝ) z
    have hz' := le_max_right (1:ℝ) z
    linarith
  have hlog : Real.log (2+z)≤Real.log 3+logPlus z := by
    calc
      _ ≤ Real.log (3*max (1:ℝ) z) := Real.log_le_log (by linarith) hzmax
      _ = _ := by rw [Real.log_mul (by norm_num) (ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left _ _))),hmax]
  have hlb : 0≤Real.logb 2 (2+z) := (Real.logb_pos (by norm_num) (by linarith : (1:ℝ)<2+z)).le
  have hceil := Nat.ceil_lt_add_one hlb
  change (covarianceDyadicCount z:ℝ)<Real.logb 2 (2+z)+1 at hceil
  have h₁ : ((covarianceDyadicCount z:ℝ)-1)*Real.log 2<Real.log (2+z) := by
    apply (lt_div_iff₀ hlog2).mp
    change (covarianceDyadicCount z:ℝ)-1<Real.logb 2 (2+z)
    linarith
  have hθ : logPlus z≤2*logPlus z*Real.log 2 := by
    nlinarith [mul_nonneg (logPlus_nonneg z) (sub_nonneg.mpr hhalf.le)]
  have hh : ((covarianceDyadicCount z:ℝ)-1)*Real.log 2<
      (2+2*logPlus z)*Real.log 2 := by nlinarith
  have hf := (mul_lt_mul_iff_left₀ hlog2).mp hh
  linarith

theorem dyadic_residual_optimized_bound {R M A d : ℝ}
    (hM : 0<M) (hA : 0<A) (hA1 : A≤1) (hd : 0≤d)
    (hbound : ∀K : ℕ,1≤K→R≤(K+1:ℝ)*(4*K/(M*A^2)+2*d*(1/2:ℝ)^K)) :
    R≤56*(1+logPlus (M*d))^2/(M*A^2) := by
  let z := M*d
  let K := covarianceDyadicCount z
  let θ := logPlus z
  have hz : 0≤z := mul_nonneg hM.le hd
  have hK1 : 1≤K := covarianceDyadicCount_pos hz
  have hpow : z≤(2:ℝ)^K := le_trans (by linarith) (covarianceDyadicCount_power hz)
  have htail : 2*d*(1/2:ℝ)^K≤2/M := by
    rw [one_div_pow]
    apply (le_div_iff₀ hM).mpr
    have hh := (div_le_one (pow_pos (by norm_num : (0:ℝ)<2) K)).mpr hpow
    change M*d/(2:ℝ)^K≤1 at hh
    have he : 2*d*(1/(2:ℝ)^K)*M=2*(M*d/(2:ℝ)^K) := by ring
    rw [he]
    linarith
  have hden : 0<M*A^2 := mul_pos hM (sq_pos_of_pos hA)
  have hA2 : A^2≤1 := pow_le_one₀ hA.le hA1
  have htail' : 2*d*(1/2:ℝ)^K≤2/(M*A^2) := htail.trans
    (div_le_div_of_nonneg_left (by norm_num) hden
      ((mul_le_mul_of_nonneg_left hA2 hM.le).trans_eq (mul_one M)))
  have hKθ : (K:ℝ)≤3+2*θ := (covarianceDyadicCount_log_bound hz).le
  have hθ : 0≤θ := logPlus_nonneg z
  have hprod : (K+1:ℝ)*(4*K+2)≤56*(1+θ)^2 := by
    have hh := mul_le_mul (by linarith : (K+1:ℝ)≤4+2*θ)
      (by linarith : (4*K+2:ℝ)≤14+8*θ) (by positivity) (by positivity)
    nlinarith [sq_nonneg θ]
  calc
    R ≤ (K+1:ℝ)*(4*K/(M*A^2)+2*d*(1/2:ℝ)^K) := hbound K hK1
    _ ≤ (K+1:ℝ)*(4*K/(M*A^2)+2/(M*A^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl htail') (by positivity)
    _ = ((K+1:ℝ)*(4*K+2))/(M*A^2) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hprod hden.le

end QuantitativeFollowup
