module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! The exact exponent optimization in Remark 8.5. These are numerical
identities and estimates; the finite-SK comparison inequality that they
will optimize is a separate theorem, not a hypothesis hidden in a rate
claim. -/
noncomputable section
namespace QuantitativeFollowup

def followupScale (x : ℝ) : ℝ := x^(-(7:ℝ)/50)

theorem followupScale_pos {x : ℝ} (hx : 0<x) : 0<followupScale x :=
  Real.rpow_pos_of_pos hx _

theorem followupScale_le_one {x : ℝ} (hx : 1≤x) : followupScale x≤1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)

theorem inv_le_followupScale {x : ℝ} (hx : 1≤x) : x⁻¹≤followupScale x := by
  rw [←Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)

theorem followupScale_pow_five {x : ℝ} (hx : 0<x) :
    (followupScale x)^5=x^(-(7:ℝ)/10) := by
  rw [followupScale,←Real.rpow_natCast,←Real.rpow_mul hx.le]
  congr 1
  norm_num

theorem followupScale_second_error {x : ℝ} (hx : 0<x) :
    x^(-(2:ℝ)/3)*(followupScale x)^((5:ℝ)/21)=x^(-(7:ℝ)/10) := by
  rw [followupScale,←Real.rpow_mul hx.le,←Real.rpow_add hx]
  congr 1
  norm_num

theorem followupScale_third_error {x : ℝ} (hx : 0<x) :
    x^(-(7:ℝ)/9)*(followupScale x)^(-(7:ℝ)/18)=x^(-(217:ℝ)/300) := by
  rw [followupScale,←Real.rpow_mul hx.le,←Real.rpow_add hx]
  congr 1
  norm_num

theorem followupScale_fourth_error {x : ℝ} (hx : 0<x) :
    x⁻¹*(followupScale x)^(-(12:ℝ)/7)=x^(-(19:ℝ)/25) := by
  rw [←Real.rpow_neg_one,followupScale,←Real.rpow_mul hx.le,←Real.rpow_add hx]
  congr 1
  norm_num

theorem followup_log_cube_bound {x : ℝ} (hx : 2≤x) :
    (Real.log (2+x))^3 ≤ (Real.log 2+50)^3*x^((3:ℝ)/50) := by
  have hp : 0<x := by linarith
  have h₁ : 1≤x^((1:ℝ)/50) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlog₂ : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hl : Real.log (2+x) ≤ (Real.log 2+50)*x^((1:ℝ)/50) := by
    calc
      _ ≤ Real.log (2*x) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2+Real.log x := Real.log_mul (by norm_num) hp.ne'
      _ ≤ Real.log 2+x^((1:ℝ)/50)/((1:ℝ)/50) :=
        add_le_add le_rfl (Real.log_le_rpow_div hp.le (by norm_num))
      _ ≤ (Real.log 2+50)*x^((1:ℝ)/50) := by
        have hh := mul_le_mul_of_nonneg_left h₁ hlog₂
        nlinarith
  have hpow := pow_le_pow_left₀ (Real.log_nonneg (by linarith : (1:ℝ) ≤ 2+x)) hl 3
  have hr : (x^((1:ℝ)/50))^3=x^((3:ℝ)/50) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hp.le]
    congr 1
    norm_num
  rw [mul_pow,hr] at hpow
  exact hpow

theorem followup_optimized_errors_bound {x : ℝ} (hx : 2≤x) :
    x^(-(7:ℝ)/10)+x^(-(2:ℝ)/3)*(followupScale x)^((5:ℝ)/21)+
      x^(-(7:ℝ)/9)*(followupScale x)^(-(7:ℝ)/18)+
      (Real.log (2+x))^3*x⁻¹*(followupScale x)^(-(12:ℝ)/7) ≤
        (3+(Real.log 2+50)^3)*x^(-(7:ℝ)/10) := by
  have hp : 0<x := by linarith
  have ht : x^(-(217:ℝ)/300) ≤ x^(-(7:ℝ)/10) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hf : (Real.log (2+x))^3*x^(-(19:ℝ)/25) ≤
      (Real.log 2+50)^3*x^(-(7:ℝ)/10) := by
    calc
      _ ≤ ((Real.log 2+50)^3*x^((3:ℝ)/50))*x^(-(19:ℝ)/25) :=
        mul_le_mul_of_nonneg_right (followup_log_cube_bound hx) (Real.rpow_nonneg hp.le _)
      _ = (Real.log 2+50)^3*x^(-(7:ℝ)/10) := by
        rw [mul_assoc,←Real.rpow_add hp]
        congr 2
        norm_num
  rw [followupScale_second_error hp,followupScale_third_error hp]
  have heq : (Real.log (2+x))^3*x⁻¹*(followupScale x)^(-(12:ℝ)/7)=
      (Real.log (2+x))^3*x^(-(19:ℝ)/25) := by
    rw [mul_assoc,followupScale_fourth_error hp]
  rw [heq]
  nlinarith

/-- For a fixed positive tilt, the literal four-term budget of Remark 8.5
is bounded by a tilt-dependent constant times `N^(-2/3)`. -/
theorem followup_fixed_tilt_errors_bound (lam : ℝ) (hlam : 0 < lam)
    {x : ℝ} (hx : 2 ≤ x) :
    x^(-(7:ℝ)/10)+x^(-(2:ℝ)/3)*lam^((5:ℝ)/21)+
      x^(-(7:ℝ)/9)*lam^(-(7:ℝ)/18)+
      (Real.log (2+x))^3*x⁻¹*lam^(-(12:ℝ)/7) ≤
      (1+lam^((5:ℝ)/21)+lam^(-(7:ℝ)/18)+
        (Real.log 2+50)^3*lam^(-(12:ℝ)/7))*x^(-(2:ℝ)/3) := by
  have hp : 0 < x := by linarith
  have h1 : 1 ≤ x := by linarith
  have hfirst : x^(-(7:ℝ)/10) ≤ x^(-(2:ℝ)/3) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  have hthird : x^(-(7:ℝ)/9)*lam^(-(7:ℝ)/18) ≤
      x^(-(2:ℝ)/3)*lam^(-(7:ℝ)/18) :=
    mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))
      (Real.rpow_nonneg hlam.le _)
  have hfourth : (Real.log (2+x))^3*x⁻¹*lam^(-(12:ℝ)/7) ≤
      (Real.log 2+50)^3*x^(-(2:ℝ)/3)*lam^(-(12:ℝ)/7) := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hlam.le _)
    calc
      _ ≤ ((Real.log 2+50)^3*x^((3:ℝ)/50))*x⁻¹ :=
        mul_le_mul_of_nonneg_right (followup_log_cube_bound hx) (inv_nonneg.mpr hp.le)
      _ = (Real.log 2+50)^3*x^(-(47:ℝ)/50) := by
        rw [mul_assoc,←Real.rpow_neg_one,←Real.rpow_add hp]
        congr 2
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)) (by positivity)
  nlinarith

end QuantitativeFollowup
