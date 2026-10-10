module
public import QuantitativeFollowup.FourTermBudgetWindowPowers
public import QuantitativePaper.SixthWindowAsymptotics

@[expose] public section

/-! Actual uniform selection of the constants in the improved tilt window.
Both the logarithmic error and diagonal correction vanish uniformly. -/
noncomputable section
open Filter
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1500000

theorem tendsto_fourTerm_window_log_cube :
    Tendsto (fun n : ℕ=>(n:ℝ)^(-(3/50:ℝ))*(Real.log (2+(n:ℝ)))^3) atTop (𝓝 0) := by
  have hh:=(QuantitativePaper.tendsto_shifted_log_rpow_nat (1/50) (by norm_num)).pow 3
  apply (show Tendsto (fun n : ℕ=>((n:ℝ)^(-(1/50:ℝ))*Real.log (2+(n:ℝ)))^3)
    atTop (𝓝 0) by simpa using hh).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  norm_num

theorem tendsto_fourTerm_window_remainder (A C : ℝ) :
    Tendsto (fun n : ℕ=>C*(A^(-5:ℝ)+A^(-(100/21:ℝ))+
      (n:ℝ)^(-(7/300:ℝ))+(n:ℝ)^(-(3/50:ℝ))*(Real.log (2+(n:ℝ)))^3)) atTop
      (𝓝 (C*(A^(-5:ℝ)+A^(-(100/21:ℝ))))) := by
  have hP:=(tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7/300)).comp
    tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def,add_zero] using
    ((tendsto_const_nhds.add hP).add tendsto_fourTerm_window_log_cube).const_mul C

theorem exists_fourTerm_window_error_cutoff (c C : ℝ) (hc : 0<c) :
    ∃A : ℝ,1≤A ∧ ∃N0 : ℕ,2≤N0 ∧ ∀n : ℕ,N0≤n →
      C*(A^(-5:ℝ)+A^(-(100/21:ℝ))+(n:ℝ)^(-(7/300:ℝ))+
        (n:ℝ)^(-(3/50:ℝ))*(Real.log (2+(n:ℝ)))^3)≤c/4 ∧
      A^(-4:ℝ)*(n:ℝ)^(-(11/25:ℝ))/4≤c/4 := by
  have hA0 : Tendsto (fun A : ℝ=>C*(A^(-5:ℝ)+A^(-(100/21:ℝ)))) atTop (𝓝 0):=by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<5)).add
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<100/21))).const_mul C
  obtain ⟨A,hsmall⟩:=eventually_atTop.1 (hA0.eventually_lt_const
    (by positivity : (0:ℝ)<c/8))
  let Ac:=max 1 A
  have hAc : 1≤Ac:=le_max_left _ _
  have hSmallAc : C*(Ac^(-5:ℝ)+Ac^(-(100/21:ℝ)))<c/8:=
    hsmall Ac (le_max_right _ _)
  have he:=(tendsto_fourTerm_window_remainder Ac C).eventually_le_const
    (show C*(Ac^(-5:ℝ)+Ac^(-(100/21:ℝ)))<c/4 by linarith)
  have hd0 : Tendsto (fun n : ℕ=>Ac^(-4:ℝ)*(n:ℝ)^(-(11/25:ℝ))/4) atTop (𝓝 0):=by
    simpa using (((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<11/25)).comp
      tendsto_natCast_atTop_atTop).const_mul (Ac^(-4:ℝ))).div_const 4
  have hd:=hd0.eventually_le_const (by positivity : (0:ℝ)<c/4)
  obtain ⟨N,hN⟩:=eventually_atTop.1 (he.and hd)
  exact ⟨Ac,hAc,max 2 N,le_max_left _ _,fun n hn=>hN n ((le_max_right _ _).trans hn)⟩

end QuantitativeFollowup
