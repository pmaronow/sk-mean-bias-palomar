module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Exact normalization of the improved comparison error on the required
N^(-2/15) tilt window. In particular, the second term is N^(-1/60),
and the logarithmic term is N^(-1/5) log(2+N). -/
noncomputable section
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem sixth_cutoff_rpow_product (N A lam u v : ℝ) (hN : 0<N) (hA : 0<A)
    (hcut : A*N^(-(2/15:ℝ))≤lam) (hv : v≤0) :
    N^u*lam^v≤A^v*N^(u+(-(2/15:ℝ))*v) := by
  have hc : 0<A*N^(-(2/15:ℝ)) := by positivity
  have hh := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hc hcut hv)
    (Real.rpow_nonneg hN.le u)
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hN.le _),←Real.rpow_mul hN.le] at hh
  convert hh using 1
  rw [show N^u*(A^v*N^(-(2/15:ℝ)*v))=A^v*(N^u*N^(-(2/15:ℝ)*v)) by ring,
    ←Real.rpow_add hN]

theorem sixth_comparison_error_normalization (N A lam E C : ℝ)
    (hN : 0<N) (hA : 0<A) (hC : 0≤C) (hlam : 0<lam)
    (hcut : A*N^(-(2/15:ℝ))≤lam)
    (herror : E≤C*(N^(-(2/3:ℝ))+N^(-(3/4:ℝ))*lam^(-(1/2:ℝ))+
      Real.log (2+N)/(N*lam))) :
    E/lam^5≤C*(A^(-(5:ℝ))+A^(-(11/2:ℝ))*N^(-(1/60:ℝ))+
      A^(-(6:ℝ))*N^(-(1/5:ℝ))*Real.log (2+N)) := by
  have h1 : N^(-(2/3:ℝ))/lam^5≤A^(-(5:ℝ)) := by
    have hh:=sixth_cutoff_rpow_product N A lam (-(2/3:ℝ)) (-(5:ℝ)) hN hA hcut (by norm_num)
    norm_num at hh
    simpa [Real.rpow_neg_one,div_eq_mul_inv] using hh
  have h2 : N^(-(3/4:ℝ))*lam^(-(1/2:ℝ))/lam^5≤A^(-(11/2:ℝ))*N^(-(1/60:ℝ)) := by
    have hh:=sixth_cutoff_rpow_product N A lam (-(3/4:ℝ)) (-(11/2:ℝ)) hN hA hcut (by norm_num)
    norm_num at hh
    rw [mul_div_assoc,←Real.rpow_natCast lam 5,←Real.rpow_sub hlam]
    norm_num
    exact hh
  have h3 : (Real.log (2+N)/(N*lam))/lam^5≤
      A^(-(6:ℝ))*N^(-(1/5:ℝ))*Real.log (2+N) := by
    have hh:=sixth_cutoff_rpow_product N A lam (-(1:ℝ)) (-(6:ℝ)) hN hA hcut (by norm_num)
    norm_num at hh
    have hlog : 0≤Real.log (2+N) := Real.log_nonneg (by linarith)
    have hp:=mul_le_mul_of_nonneg_right hh hlog
    have he : (Real.log (2+N)/(N*lam))/lam^5=
        (N^(-(1:ℝ))*lam^(-(6:ℝ)))*Real.log (2+N) := by
      norm_num [Real.rpow_neg_one]
      field_simp <;> ring
    rw [he]
    simpa [Real.rpow_neg_one] using hp
  have he:=div_le_div_of_nonneg_right herror (pow_nonneg hlam.le 5)
  rw [mul_div_assoc,add_div,add_div] at he
  exact he.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) hC)

theorem sixth_diagonal_error_normalization (N A lam : ℝ) (hN : 0<N) (hA : 0<A)
    (hlam : 0<lam) (hcut : A*N^(-(2/15:ℝ))≤lam) :
    (lam^2/4)/(N*lam^6)≤(1/4:ℝ)*A^(-(4:ℝ))*N^(-(7/15:ℝ)) := by
  have hh:=sixth_cutoff_rpow_product N A lam (-(1:ℝ)) (-(4:ℝ)) hN hA hcut (by norm_num)
  norm_num at hh
  have hm:=mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤1/4)
  have he : (lam^2/4)/(N*lam^6)=(1/4:ℝ)*(N^(-(1:ℝ))*lam^(-(4:ℝ))) := by
    norm_num [Real.rpow_neg_one]
    field_simp <;> ring
  rw [he]
  simpa [Real.rpow_neg_one,mul_assoc] using hm

end QuantitativePaper
