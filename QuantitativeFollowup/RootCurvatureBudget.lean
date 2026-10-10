module
public import QuantitativeFollowup.RootRateArithmetic
public import FourPapersCommon.MiddleCurvature

@[expose] public section

/-! Exact root-localization budget constants. Actual functional response
is kept separate: a genuine middle-interval curvature bound, convexity
and the two endpoint budgets imply the displayed balance coefficient. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1500000

theorem root_midpoint_budget (q eta f₀ f₁ m : ℝ) (hq : q ∈ Ioc (0 : ℝ) (1/4))
    (heta : 0 ≤ eta) (h₀ : f₀ ≤ m+eta/12)
    (h₁ : f₁ ≤ m+eta+45*eta/(4*q)) :
    f₀+f₁-2*m ≤ 12*eta/q := by
  have hAlgebra : (13*eta/12+45*eta/(4*q))*q=13*eta*q/12+45*eta/4 := by
    field_simp [hq.1.ne']
  have hScale : 13*eta*q/12+45*eta/4 ≤ 12*eta := by
    nlinarith [mul_le_mul_of_nonneg_left hq.2 heta]
  have hBound : 13*eta/12+45*eta/(4*q) ≤ 12*eta/q := by
    apply (le_div_iff₀ hq.1).mpr
    rwa [hAlgebra]
  linarith

theorem root_balance_of_midpoint_budget (q eta rho k beta d f₀ f₁ m : ℝ)
    (hq : q ∈ Ioc (0 : ℝ) (1/4)) (heta : 0 ≤ eta) (hrho : 0 < rho) (hk : 0 < k)
    (h₀ : f₀ ≤ m+eta/12) (h₁ : f₁ ≤ m+eta+45*eta/(4*q))
    (hGap : (3/16 : ℝ)*(rho*k^2*q^2/4608)*
      min (7*q^3/(3840*beta)) (2*q/(15*d)) ≤ f₀+f₁-2*m) :
    min (7*q^3/(3840*beta)) (2*q/(15*d)) ≤ (294912/k^2)*eta/(rho*q^3) := by
  have hBudget := root_midpoint_budget q eta f₀ f₁ m hq heta h₀ h₁
  have hScale := mul_le_mul_of_nonneg_right (hGap.trans hBudget) hq.1.le
  have hRight : (12*eta/q)*q=12*eta := by field_simp [hq.1.ne']
  rw [hRight] at hScale
  have hDen : 0 < rho*k^2*q^3 := by positivity [hq.1]
  have hBalance : min (7*q^3/(3840*beta)) (2*q/(15*d)) ≤ 294912*eta/(rho*k^2*q^3) := by
    apply (le_div_iff₀ hDen).mpr
    nlinarith
  convert hBalance using 1
  field_simp

theorem root_balance_of_middle_curvature (q eta rho k beta d m : ℝ)
    (hq : q ∈ Ioc (0 : ℝ) (1/4)) (heta : 0 ≤ eta) (hrho : 0 < rho) (hk : 0 < k)
    (f f' f'' : ℝ → ℝ) (hConvex : ConvexOn ℝ (Icc (0 : ℝ) 1) f)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf' : ∀x∈Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf'' : ∀x∈Ioo (1/4 : ℝ) (3/4), HasDerivAt f' (f'' x) x)
    (hCurvature : ∀x∈Ioo (1/4 : ℝ) (3/4),
      (rho*k^2*q^2/4608)*min (7*q^3/(3840*beta)) (2*q/(15*d)) ≤ f'' x)
    (hMin : m ≤ f (1/2)) (h₀ : f 0 ≤ m+eta/12)
    (h₁ : f 1 ≤ m+eta+45*eta/(4*q)) :
    min (7*q^3/(3840*beta)) (2*q/(15*d)) ≤ (294912/k^2)*eta/(rho*q^3) := by
  have hGap := FourPapersCommon.midpoint_minimum_gap_of_middle_curvature f f' f''
    ((rho*k^2*q^2/4608)*min (7*q^3/(3840*beta)) (2*q/(15*d))) m
    hConvex hf hf' hf'' hCurvature hMin
  apply root_balance_of_midpoint_budget q eta rho k beta d (f 0) (f 1) m
    hq heta hrho hk h₀ h₁
  convert hGap using 1
  ring

end QuantitativeFollowup
