module
public import FourPapersCommon.IntegralGronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

@[expose] public section

/-! A pathwise temperature comparison for measurable-time integral states.
The estimate uses the target drift's Lipschitz constant and is uniform in
the cumulative-mass coefficient. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace FourPapersCommon
set_option maxHeartbeats 700000

theorem integral_state_temperature_bound (β γ h : ℝ) (α : ℝ→ℝ)
    (hα : Measurable α) (hα0 : ∀r,0≤α r) (hα1 : ∀r,α r≤1)
    (v w : ℝ→ℝ→ℝ) (hv : Continuous (Function.uncurry v))
    (hw : Continuous (Function.uncurry w))
    (hv1 : ∀r x,‖v r x‖≤1) (hw1 : ∀r x,‖w r x‖≤1)
    (hwL : ∀r,LipschitzWith 1 (w r)) (D : ℝ) (hD : 0≤D)
    (hvw : ∀r x,‖v r x-w r x‖≤D)
    (W X Y : ℝ→ℝ) (hX : Continuous X) (hY : Continuous Y)
    (N : ℝ) (hN : 0≤N) (hW : ∀r∈Icc (0 : ℝ) 1,‖W r‖≤N)
    (hXe : ∀r∈Icc (0 : ℝ) 1,X r=h+β*W r+∫s in 0..r,β^2*α s*v s (X s))
    (hYe : ∀r∈Icc (0 : ℝ) 1,Y r=h+γ*W r+∫s in 0..r,γ^2*α s*w s (Y s)) :
    ∀r∈Icc (0 : ℝ) 1,‖X r-Y r‖≤
      (|β-γ| *N+|β^2-γ^2|+γ^2*D)*Real.exp (γ^2) := by
  let f:=fun r=>‖X r-Y r‖
  let δ:=|β-γ| *N+|β^2-γ^2|+γ^2*D
  have hδ : 0≤δ := by dsimp [δ]; positivity
  have hCTS : Continuous f := (hX.sub hY).norm
  have hIi (b : ℝ) (r : ℝ) (U : ℝ→ℝ) (hU : Continuous U)
      (g : ℝ→ℝ→ℝ) (hg : Continuous (Function.uncurry g)) (hg1 : ∀t x,‖g t x‖≤1) :
      IntervalIntegrable (fun s=>b^2*α s*g s (U s)) volume 0 r := by
    apply (intervalIntegrable_const (c:=(b^2 : ℝ))).mono_fun'
      (((measurable_const.mul hα).mul (hg.measurable.comp (measurable_id.prodMk hU.measurable))).aestronglyMeasurable)

    exact .of_forall fun s=>by
      change ‖b^2*α s*g s (U s)‖≤b^2
      rw [norm_mul,norm_mul,Real.norm_of_nonneg (sq_nonneg b),Real.norm_of_nonneg (hα0 s)]
      simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left (((mul_le_mul (hα1 s) (hg1 s (U s)) (norm_nonneg _) zero_le_one).trans_eq (mul_one _)))
        (sq_nonneg b)).trans_eq (mul_one _)
  have hpoint (s : ℝ) :
      ‖β^2*α s*v s (X s)-γ^2*α s*w s (Y s)‖≤|β^2-γ^2|+γ^2*D+γ^2*f s := by
    have hwxy := (hwL s).norm_sub_le (X s) (Y s)
    simp only [NNReal.coe_one,one_mul] at hwxy
    have hvwxy : ‖v s (X s)-w s (Y s)‖≤D+f s := by
      rw [show v s (X s)-w s (Y s) = (v s (X s)-w s (X s))+(w s (X s)-w s (Y s)) by ring]
      exact (norm_add_le _ _).trans (add_le_add (hvw s _) hwxy)
    rw [show β^2*α s*v s (X s)-γ^2*α s*w s (Y s) =
      (β^2-γ^2)*(α s*v s (X s))+γ^2*α s*(v s (X s)-w s (Y s)) by ring]
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Real.norm_of_nonneg (hα0 s),Real.norm_of_nonneg (sq_nonneg γ),Real.norm_eq_abs]
    have ha : α s*‖v s (X s)‖≤1 := ((mul_le_mul (hα1 s) (hv1 s _) (norm_nonneg _) zero_le_one).trans_eq (mul_one _))
    have hb : α s*‖v s (X s)-w s (Y s)‖≤D+f s := by
      exact (mul_le_mul_of_nonneg_left hvwxy (hα0 s)).trans
        ((mul_le_mul_of_nonneg_right (hα1 s) (add_nonneg hD (norm_nonneg _))).trans_eq (one_mul _))
    simp only [Real.norm_eq_abs] at ha hb
    nlinarith [mul_le_mul_of_nonneg_left ha (abs_nonneg (β^2-γ^2)),
      mul_le_mul_of_nonneg_left hb (sq_nonneg γ)]
  have hineq (r : ℝ) (hr : r∈Icc (0 : ℝ) 1) : f r≤δ+γ^2*(∫s in 0..r,f s) := by
    have hvI := hIi β r X hX v hv hv1
    have hwI := hIi γ r Y hY w hw hw1
    have hi : IntervalIntegrable (fun s=>|β^2-γ^2|+γ^2*D+γ^2*f s) volume 0 r :=
      intervalIntegrable_const.add ((hCTS.intervalIntegrable 0 r).const_mul (γ^2))
    have hh := intervalIntegral.integral_mono_on hr.1 (hvI.sub hwI).norm hi (fun s _=>hpoint s)
    change ‖X r-Y r‖≤δ+γ^2*(∫s in 0..r,f s)
    rw [hXe r hr,hYe r hr,show (h+β*W r+∫s in 0..r,β^2*α s*v s (X s))-
        (h+γ*W r+∫s in 0..r,γ^2*α s*w s (Y s)) =
      (β-γ)*W r+((∫s in 0..r,β^2*α s*v s (X s))-(∫s in 0..r,γ^2*α s*w s (Y s))) by ring,
      ←intervalIntegral.integral_sub hvI hwI]
    change ‖(β-γ)*W r+∫s in 0..r,β^2*α s*v s (X s)-γ^2*α s*w s (Y s)‖≤δ+γ^2*(∫s in 0..r,f s)
    apply (norm_add_le _ _).trans
    have hnoise : ‖(β-γ)*W r‖≤|β-γ| *N := by
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hW r hr) (abs_nonneg _)
    have hn := intervalIntegral.norm_integral_le_integral_norm (μ:=volume) hr.1
      (f:=fun s=>β^2*α s*v s (X s)-γ^2*α s*w s (Y s))
    have hs := hn.trans hh
    rw [intervalIntegral.integral_add intervalIntegrable_const ((hCTS.intervalIntegrable 0 r).const_mul _),
      intervalIntegral.integral_const,intervalIntegral.integral_const_mul] at hs
    simp only [sub_zero,smul_eq_mul] at hs
    have hc : 0≤|β^2-γ^2|+γ^2*D := by positivity
    simp only [Real.norm_eq_abs] at hnoise hs
    dsimp [δ]
    nlinarith [mul_le_mul_of_nonneg_right hr.2 hc]
  have hg := le_exp_of_integral_le f hCTS 1 δ (γ^2) hδ (sq_nonneg γ)
    (fun r _=>norm_nonneg _) hineq
  intro r hr
  exact (hg r hr).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hr.2 (sq_nonneg γ)])) hδ)

end FourPapersCommon
