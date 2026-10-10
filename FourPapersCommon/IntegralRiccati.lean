module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-! Reciprocal integration for an actual absolutely continuous nonnegative
decay curve. Measurable reaction coefficients and endpoint zeros are allowed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem lipschitzOnWith_inverse_positive_ray (c : ℝ) (hc : 0 < c) :
    LipschitzOnWith (Real.toNNReal (1 / c^2)) (fun x : ℝ => x⁻¹) (Ici c) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  simp only [Real.coe_toNNReal', max_eq_left (by positivity : (0 : ℝ) ≤ 1 / c^2)]
  intro x hx y hy
  have hx0 : 0 < x := hc.trans_le hx
  have hy0 : 0 < y := hc.trans_le hy
  rw [dist_inv_inv₀ hx0.ne' hy0.ne', Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hx0, abs_of_pos hy0]
  have hp : c^2 ≤ x*y := by
    simpa only [pow_two] using mul_le_mul hx hy hc.le hx0.le
  calc
    dist x y / (x*y) ≤ dist x y / c^2 :=
      div_le_div_of_nonneg_left dist_nonneg (sq_pos_of_pos hc) hp
    _ = (1 / c^2) * dist x y := by ring

theorem integral_riccati_bound {φ f g : ℝ → ℝ} {r q B : ℝ}
    (hrq : r ≤ q) (hB : 0 < B)
    (hφ : AbsolutelyContinuousOnInterval φ r q)
    (hmono : AntitoneOn φ (Icc r q))
    (hnonneg : ∀ x ∈ Icc r q, 0 ≤ φ x)
    (hder : ∀ᵐ x : ℝ, x ∈ Icc r q → HasDerivAt φ (-f x) x)
    (hreact : ∀ᵐ x : ℝ, x ∈ Icc r q → g x * (φ x)^2 ≤ B * f x)
    (hg : IntervalIntegrable g volume r q)
    (hden : 0 < ∫ x in r..q, g x) :
    φ q ≤ B / (∫ x in r..q, g x) := by
  have hqmem : q ∈ Icc r q := ⟨hrq, le_rfl⟩
  by_cases hzero : φ q = 0
  · rw [hzero]
    exact div_nonneg hB.le hden.le
  have hq : 0 < φ q := lt_of_le_of_ne (hnonneg q hqmem) (Ne.symm hzero)
  have hlower (x : ℝ) (hx : x ∈ Icc r q) : φ q ≤ φ x :=
    hmono hx hqmem hx.2
  let ψ := fun x : ℝ => (φ x)⁻¹
  have hmap : MapsTo φ (uIcc r q) (Ici (φ q)) := by
    intro x hx
    rw [uIcc_of_le hrq] at hx
    exact hlower x hx
  have hψ : AbsolutelyContinuousOnInterval ψ r q :=
    (lipschitzOnWith_inverse_positive_ray (φ q) hq).comp_absolutelyContinuousOnInterval hmap hφ
  have hae : ∀ᵐ x : ℝ, x ∈ Icc r q → g x / B ≤ deriv ψ x := by
    filter_upwards [hder, hreact] with x hd hr hx
    have hx0 : 0 < φ x := hq.trans_le (hlower x hx)
    have hdi := (hd hx).inv hx0.ne'
    have hde : deriv ψ x = f x / (φ x)^2 := by
      have he : ψ = φ⁻¹ := by funext y; rfl
      rw [he]
      simpa only [neg_neg] using hdi.deriv
    rw [hde]
    exact (div_le_div_iff₀ hB (sq_pos_of_pos hx0)).mpr (by simpa only [mul_comm] using hr hx)
  have hi := intervalIntegral.integral_mono_ae_restrict hrq (hg.div_const B)
    hψ.intervalIntegrable_deriv ((ae_restrict_iff' measurableSet_Icc).mpr hae)
  rw [intervalIntegral.integral_div, hψ.integral_deriv_eq_sub] at hi
  have hrpos : 0 < φ r := hq.trans_le (hlower r ⟨le_rfl, hrq⟩)
  have hI : (∫ x in r..q, g x) / B ≤ (φ q)⁻¹ := by
    change (∫ x in r..q, g x) / B ≤ (φ q)⁻¹ - (φ r)⁻¹ at hi
    linarith [inv_nonneg.mpr hrpos.le]
  have hD := (div_le_iff₀ hB).mp hI
  have hm := mul_le_mul_of_nonneg_left hD hq.le
  have hp : φ q * (∫ x in r..q, g x) ≤ B := by
    simpa only [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] using hm
  exact (le_div_iff₀ hden).mpr hp

end FourPapersCommon
