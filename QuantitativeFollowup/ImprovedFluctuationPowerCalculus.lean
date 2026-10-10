module
public import QuantitativePaper.UniformEnergyPowerCalculus

@[expose] public section

/-! General exponent arithmetic for the genuine five-fourths
variance/mean inequality. This includes both printed improved exponents. -/
noncomputable section
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

theorem variance_upper_of_mean_exponent (N V M c C a : ℝ) (hN : 0<N) (hV : 0 ≤ V)
    (hc : 0<c) (hC : 0<C) (hshort : c*((V+1/2)/N)^(5/4:ℝ) ≤ M)
    (hmean : M ≤ C*N^(-a)) : V ≤ (C/c)^(4/5:ℝ)*N^(1-(4/5:ℝ)*a) := by
  have hv : 0<(V+1/2)/N:=by positivity
  have hbase : ((V+1/2)/N)^(5/4:ℝ) ≤ (C/c)*N^(-a):=by
    rw [show (C/c)*N^(-a)=(C*N^(-a))/c by ring]
    apply (le_div_iff₀ hc).mpr
    nlinarith
  have hh:=Real.rpow_le_rpow (Real.rpow_nonneg hv.le _) hbase (by norm_num : (0:ℝ) ≤ 4/5)
  rw [←Real.rpow_mul hv.le,show (5/4:ℝ)*(4/5)=1 by norm_num,Real.rpow_one,
    Real.mul_rpow (by positivity) (Real.rpow_nonneg hN.le _),←Real.rpow_mul hN.le] at hh
  have hm:=(div_le_iff₀ hN).mp hh
  have he : (C/c)^(4/5:ℝ)*N^((-a)*(4/5:ℝ))*N=(C/c)^(4/5:ℝ)*N^(1-(4/5:ℝ)*a):=by
    calc
      _=(C/c)^(4/5:ℝ)*(N^((-a)*(4/5:ℝ))*N^(1:ℝ)):=by rw [Real.rpow_one];ring
      _=_:=by rw [←Real.rpow_add hN];congr 2 <;> ring
  rw [he] at hm
  linarith

theorem mean_lower_of_variance_exponent (N V M c k b : ℝ) (hN : 0<N)
    (hc : 0 ≤ c) (hk : 0<k) (hV : k*N^b ≤ V)
    (hshort : c*((V+1/2)/N)^(5/4:ℝ) ≤ M) :
    c*k^(5/4:ℝ)*N^((b-1)*(5/4:ℝ)) ≤ M := by
  have hbase : k*N^(b-1) ≤ (V+1/2)/N:=by
    apply (le_div_iff₀ hN).mpr
    have he : k*N^(b-1)*N=k*N^b:=by
      calc
        _=k*(N^(b-1)*N^(1:ℝ)):=by rw [Real.rpow_one];ring
        _=_:=by rw [←Real.rpow_add hN];congr 2 <;> ring
    rw [he]
    linarith
  have hh:=Real.rpow_le_rpow (by positivity : 0 ≤ k*N^(b-1)) hbase (by norm_num : (0:ℝ) ≤ 5/4)
  rw [Real.mul_rpow hk.le (Real.rpow_nonneg hN.le _),←Real.rpow_mul hN.le] at hh
  simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hh hc).trans hshort

end QuantitativeFollowup
