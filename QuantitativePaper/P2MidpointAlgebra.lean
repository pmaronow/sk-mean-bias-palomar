module
public import QuantitativePaper.P2SmoothingWidth
public import QuantitativePaper.ResponseCurvatureLower

@[expose] public section

/-! Scalar normalization of the physical quartic response bounds. -/
noncomputable section
open Set
namespace QuantitativePaper
set_option maxHeartbeats 1000000

def p2MidpointConstant (k Cs : ℝ) : ℝ :=
  (responseCurvatureConstant 2)^4*k^2/(3600*(32+2*Cs))

theorem p2_denominator_scaling_bound (r q Cs Δ : ℝ)
    (hr : r ∈ Ioc (0 : ℝ) 1) (hq : q ∈ Ioc (0 : ℝ) (1/4))
    (hCs : 0 ≤ Cs) (hΔ : Δ ∈ Icc (0 : ℝ) 1) :
    (2/(Real.sqrt r*Real.sqrt q))*512/(105*(q/2))+
      2*(Cs+1/(Real.sqrt r*q*Real.sqrt q))*Δ ≤
      (32+2*Cs)/(Real.sqrt r*q*Real.sqrt q) := by
  let A := Real.sqrt r*q*Real.sqrt q
  have hA : 0 < A := by dsimp [A];positivity [hr.1,hq.1]
  have hru : Real.sqrt r ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hr.2
  have hqu : Real.sqrt q ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (show q ≤ 1 by linarith [hq.2])
  have hAle : A ≤ 1 := by
    dsimp [A]
    calc
      _ ≤ 1*q*1 := mul_le_mul (mul_le_mul_of_nonneg_right hru hq.1.le) hqu
        (Real.sqrt_nonneg q) (by positivity [hq.1])
      _ ≤ 1 := by linarith [hq.2]
  have hd : 0 ≤ Cs+1/A := by positivity
  have hD := mul_le_mul_of_nonneg_left hΔ.2 (show 0 ≤ 2*(Cs+1/A) by positivity)
  have hfirst : ((2/(Real.sqrt r*Real.sqrt q))*512/(105*(q/2)))*A = 2048/105 := by
    dsimp [A]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hr.1),ne_of_gt (Real.sqrt_pos.2 hq.1),ne_of_gt hq.1]
    <;> ring
  apply (le_div_iff₀ hA).mpr
  have hmul := mul_le_mul_of_nonneg_right hD hA.le
  have he : (2*(Cs+1/A))*A = 2*(Cs*A+1) := by field_simp [hA.ne']
  simp only [mul_one] at hmul
  rw [he] at hmul
  have hCA := mul_le_mul_of_nonneg_left hAle hCs
  change (_+2*(Cs+1/A)*Δ)*A ≤ 32+2*Cs
  rw [add_mul,hfirst]
  nlinarith only [hmul,hCA]

theorem p2_curvature_coefficient_identity (r q k Cs : ℝ) (hr : 0 < r) (hq : 0 < q)
    (hCs : 0 ≤ Cs) :
    (4*p2MidpointConstant k Cs*r^3*Real.sqrt r*q^5*Real.sqrt q)*
      ((32+2*Cs)/(Real.sqrt r*q*Real.sqrt q)) =
      r^3*((responseCurvatureConstant 2)^2*k*q^2/30)^2 := by
  unfold p2MidpointConstant
  field_simp
  ring

end QuantitativePaper
