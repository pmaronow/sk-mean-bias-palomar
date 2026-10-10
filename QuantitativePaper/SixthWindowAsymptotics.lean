module
public import QuantitativePaper.SixthWindowComparisonScale
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! Uniform selection of the tilt cutoff and system-size threshold for the
literal improved comparison estimate. The logarithmic remainder and the
diagonal completion are controlled on the entire tilt window. -/
noncomputable section
open Filter
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1200000

theorem tendsto_shifted_log_rpow_nat (r : ℝ) (hr : 0<r) :
    Tendsto (fun n : ℕ=>(n:ℝ)^(-r)*Real.log (2+(n:ℝ))) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ=>(n:ℝ)^(-r)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ=>(n:ℝ)^(-r)*Real.log (n:ℝ)) atTop (𝓝 0) := by
    have hh := ((isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hnR : 0<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    simp only [Function.comp_def,Real.rpow_neg hnR.le,div_eq_mul_inv,mul_comm]
  apply squeeze_zero' ?_ ?_ (show Tendsto
    (fun n : ℕ=>(n:ℝ)^(-r)*Real.log 3+(n:ℝ)^(-r)*Real.log (n:ℝ))
    atTop (𝓝 0) by simpa using (hp.mul_const (Real.log 3)).add hl)
  · exact .of_forall fun n=>mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hnR : (1:ℝ)≤n := by exact_mod_cast hn
    have hnp : 0<(n:ℝ) := by linarith
    have hlog : Real.log (2+(n:ℝ))≤Real.log 3+Real.log (n:ℝ) := by
      rw [←Real.log_mul (by norm_num : (3:ℝ)≠0) hnp.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    simpa only [mul_add] using mul_le_mul_of_nonneg_left hlog
      (Real.rpow_nonneg hnp.le (-r))

theorem tendsto_sixth_comparison_remainder (A C : ℝ) :
    Tendsto (fun n : ℕ=>C*(A^(-(5:ℝ))+A^(-(11/2:ℝ))*(n:ℝ)^(-(1/60:ℝ))+
      A^(-(6:ℝ))*(n:ℝ)^(-(1/5:ℝ))*Real.log (2+(n:ℝ)))) atTop
      (𝓝 (C*A^(-(5:ℝ)))) := by
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/60)).comp
    tendsto_natCast_atTop_atTop
  have h2 := tendsto_shifted_log_rpow_nat (1/5) (by norm_num)
  simpa only [Function.comp_def,mul_zero,add_zero,mul_assoc] using
    ((tendsto_const_nhds.add (h1.const_mul (A^(-(11/2:ℝ))))).add
      (h2.const_mul (A^(-(6:ℝ))))).const_mul C

theorem exists_sixth_window_error_cutoff (c0 C : ℝ) (hc0 : 0<c0) (hC : 0≤C) :
    ∃A : ℝ,0<A ∧ ∃N0 : ℕ,1≤N0 ∧ ∀n : ℕ,N0≤n→
      C*(A^(-(5:ℝ))+A^(-(11/2:ℝ))*(n:ℝ)^(-(1/60:ℝ))+
        A^(-(6:ℝ))*(n:ℝ)^(-(1/5:ℝ))*Real.log (2+(n:ℝ)))≤c0/4 ∧
      (1/4:ℝ)*A^(-(4:ℝ))*(n:ℝ)^(-(7/15:ℝ))≤c0/4 := by
  have hA0 : Tendsto (fun A : ℝ=>C*A^(-(5:ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<5)).const_mul C
  obtain ⟨A,hsmall⟩ := eventually_atTop.1
    (hA0.eventually_lt_const (by positivity : (0:ℝ)<c0/8))
  let Ac := max 1 A
  have hAc : 0<Ac := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hsmallAc : C*Ac^(-(5:ℝ))<c0/8 := hsmall Ac (le_max_right _ _)
  have he := (tendsto_sixth_comparison_remainder Ac C).eventually_le_const
    (show C*Ac^(-(5:ℝ))<c0/4 by linarith)
  have hd0 : Tendsto (fun n : ℕ=>(1/4:ℝ)*Ac^(-(4:ℝ))*(n:ℝ)^(-(7/15:ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7/15)).comp
      tendsto_natCast_atTop_atTop).const_mul ((1/4:ℝ)*Ac^(-(4:ℝ)))
  have hd := hd0.eventually_le_const (by positivity : (0:ℝ)<c0/4)
  obtain ⟨N,hN⟩:=eventually_atTop.1 (he.and hd)
  refine ⟨Ac,hAc,max 1 N,le_max_left _ _,?_⟩
  intro n hn
  exact hN n ((le_max_right _ _).trans hn)

end QuantitativePaper
