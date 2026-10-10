module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Exact fluctuation exponent algebra, applied downstream to the actual
SK mean, variance, and tail estimates. -/
noncomputable section
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem variance_upper_of_mean_power (N V M c C : ℝ) (hN : 0<N) (hV : 0≤V)
    (hc : 0<c) (hC : 0<C)
    (hshort : c*((V+1/2)/N)^(5/4:ℝ)≤M) (hmean : M≤C*N^(-(2/3:ℝ))) :
    V≤(C/c)^(4/5:ℝ)*N^(7/15:ℝ) := by
  have hv : 0<(V+1/2)/N := by positivity
  have hbase : ((V+1/2)/N)^(5/4:ℝ)≤(C/c)*N^(-(2/3:ℝ)) := by
    rw [show (C/c)*N^(-(2/3:ℝ))=(C*N^(-(2/3:ℝ)))/c by ring]
    apply (le_div_iff₀ hc).mpr
    nlinarith
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hv.le _) hbase
    (by norm_num : (0:ℝ)≤4/5)
  rw [←Real.rpow_mul hv.le,show (5/4:ℝ)*(4/5)=1 by norm_num,Real.rpow_one,
    Real.mul_rpow (by positivity) (Real.rpow_nonneg hN.le _),←Real.rpow_mul hN.le] at hh
  norm_num at hh
  have hm := (div_le_iff₀ hN).mp hh
  have he : (C/c)^(4/5:ℝ)*N^(-(8/15:ℝ))*N=(C/c)^(4/5:ℝ)*N^(7/15:ℝ) := by
    calc
      _=(C/c)^(4/5:ℝ)*(N^(-(8/15:ℝ))*N^(1:ℝ)) := by rw [Real.rpow_one];ring
      _=_ := by rw [←Real.rpow_add hN];norm_num
  rw [he] at hm
  linarith

theorem mean_lower_of_variance_power (N V M c k : ℝ) (hN : 0<N) (hc : 0≤c)
    (hk : 0<k) (hV : k*N^(4/15:ℝ)≤V)
    (hshort : c*((V+1/2)/N)^(5/4:ℝ)≤M) :
    c*k^(5/4:ℝ)*N^(-(11/12:ℝ))≤M := by
  have hbase : k*N^(-(11/15:ℝ))≤(V+1/2)/N := by
    apply (le_div_iff₀ hN).2
    have he : k*N^(-(11/15:ℝ))*N=k*N^(4/15:ℝ) := by
      calc
        _=k*(N^(-(11/15:ℝ))*N^(1:ℝ)) := by rw [Real.rpow_one];ring
        _=_ := by rw [←Real.rpow_add hN];norm_num
    rw [he]
    linarith
  have hh := Real.rpow_le_rpow (by positivity : 0≤k*N^(-(11/15:ℝ))) hbase
    (by norm_num : (0:ℝ)≤5/4)
  rw [Real.mul_rpow hk.le (Real.rpow_nonneg hN.le _),←Real.rpow_mul hN.le] at hh
  norm_num at hh
  have hm := (mul_le_mul_of_nonneg_left hh hc).trans hshort
  simpa only [mul_assoc] using hm

theorem tail_scale_lower (N D A B : ℝ) (hN : 0<N) (hD : 0<D) (hA : 0<A)
    (hB : 0<B) (htails : Real.exp (-A*N^(1/5:ℝ))≤3*Real.exp (-B*N^(1/3:ℝ)/D))
    (hlog : Real.log 3≤A*N^(1/5:ℝ)) :
    B/(2*A)*N^(2/15:ℝ)≤D := by
  have hexp : 3*Real.exp (-B*N^(1/3:ℝ)/D)=
      Real.exp (Real.log 3-B*N^(1/3:ℝ)/D) := by
    rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<3)]
    congr 2
    ring
  rw [hexp] at htails
  have hh := Real.exp_le_exp.mp htails
  have hb : B*N^(1/3:ℝ)≤2*A*N^(1/5:ℝ)*D := by
    have hr : B*N^(1/3:ℝ)/D≤2*A*N^(1/5:ℝ) := by linarith
    exact (div_le_iff₀ hD).mp hr
  have he : N^(1/3:ℝ)=N^(2/15:ℝ)*N^(1/5:ℝ) := by
    rw [←Real.rpow_add hN]
    norm_num
  rw [he] at hb
  have hnRoot : 0<N^(1/5:ℝ) := Real.rpow_pos_of_pos hN _
  have hs : B*N^(2/15:ℝ)≤2*A*D := by nlinarith
  rw [show B/(2*A)*N^(2/15:ℝ)=(B*N^(2/15:ℝ))/(2*A) by ring]
  apply (div_le_iff₀ (by positivity : 0<2*A)).2
  nlinarith

theorem variance_lower_of_tail_scale (N D V d R : ℝ) (hN : 0<N) (hd : 0<d)
    (hD : 0≤D) (hscale : d*N^(2/15:ℝ)≤D)
    (hV : D^2=V+R) (hR : R≤1) (hsize : 2≤d^2*N^(4/15:ℝ)) :
    d^2/2*N^(4/15:ℝ)≤V := by
  have hp := pow_le_pow_left₀ (by positivity : 0≤d*N^(2/15:ℝ)) hscale 2
  rw [mul_pow,←Real.rpow_mul_natCast hN.le] at hp
  norm_num at hp
  nlinarith

end QuantitativePaper
