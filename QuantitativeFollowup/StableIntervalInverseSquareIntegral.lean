module
public import QuantitativeFollowup.StableIntervalCutoff
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! The literal inverse-square stable-interval integral, including the
closed upper cutoff and the actual lambda-dependent cutoff lower bound. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 500000

theorem stableInterval_inverseSquare_intervalIntegrable (a : ℝ) (ha : 0<a) (ha1 : a ≤ 1) :
    IntervalIntegrable (fun rho : ℝ=>1/rho^2) volume a 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
  intro x hx
  rw [uIcc_of_le ha1] at hx
  exact pow_ne_zero 2 (ne_of_gt (ha.trans_le hx.1))

theorem stableInterval_inverseSquare_integral (a : ℝ) (ha : 0<a) (ha1 : a ≤ 1) :
    (∫rho in a..(1:ℝ),1/rho^2)=a⁻¹-1 := by
  have hzero : (0:ℝ)∉uIcc a 1 := by
    rw [uIcc_of_le ha1]
    intro h
    linarith [h.1]
  have hh := integral_rpow (a:=a) (b:=(1:ℝ)) (r:=(-2:ℝ))
    (Or.inr ⟨by norm_num,hzero⟩)
  have he : (∫rho in a..(1:ℝ),rho^(-2:ℝ))=(∫rho in a..(1:ℝ),1/rho^2) := by
    apply intervalIntegral.integral_congr
    intro rho hrho
    rw [uIcc_of_le ha1] at hrho
    change rho^(-2:ℝ)=1/rho^2
    rw [Real.rpow_neg (ha.le.trans hrho.1),Real.rpow_two,one_div]
  rw [he] at hh
  norm_num only at hh
  rw [Real.rpow_neg_one] at hh
  calc
    _=(1-a⁻¹)/(-1):=hh
    _=a⁻¹-1:=by ring

theorem stableInterval_integral_of_inverseSquare_bound
    (D : ℝ → ℝ) (a B : ℝ) (ha : 0<a) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    (hi : IntervalIntegrable D volume a 1)
    (hb : ∀ᵐrho ∂volume,rho∈Ioo a 1 → D rho ≤ B/rho^2) :
    (∫rho in a..(1:ℝ),D rho) ≤ B/a := by
  have hG : IntervalIntegrable (fun rho : ℝ=>B/rho^2) volume a 1 := by
    simpa only [mul_one_div] using (stableInterval_inverseSquare_intervalIntegrable a ha ha1).const_mul B
  have hbound : (∫rho in a..(1:ℝ),D rho) ≤ ∫rho in a..(1:ℝ),B/rho^2 := by
    apply intervalIntegral.integral_mono_ae_restrict ha1 hi hG
    change ∀ᵐrho ∂volume.restrict (Icc a 1),D rho ≤ B/rho^2
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hb,volume.ae_ne a,volume.ae_ne (1:ℝ)] with rho hr hnea hne1 hmem
    exact hr ⟨lt_of_le_of_ne hmem.1 hnea.symm,lt_of_le_of_ne hmem.2 hne1⟩
  have he : (∫rho in a..(1:ℝ),B/rho^2)=B*(a⁻¹-1) := by
    calc
      _=B*(∫rho in a..(1:ℝ),1/rho^2):=by simp only [div_eq_mul_inv,one_mul,intervalIntegral.integral_const_mul]
      _=B*(a⁻¹-1):=by rw [stableInterval_inverseSquare_integral a ha ha1]
  rw [he] at hbound
  exact hbound.trans (by rw [div_eq_mul_inv];nlinarith)

end QuantitativeFollowup
