module
public import QuantitativeFollowup.SmallIntervalIntegralPowers

@[expose] public section

/-! Integrating the two honest small-interval envelopes. The model file
supplies these envelopes from true minima and an actual trial budget. -/
noncomputable section
open Set Filter MeasureTheory FourPapersCommon
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000

 theorem smallInterval_moving_integral_le (N C b : ℝ) (hN : 0<N)
    (hC : 0≤C) (hb : 0≤b) (hcut : b≤1/N)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 b)
    (hbound : ∀ᵐrho∂volume.restrict (Ioo (0:ℝ) b),f rho≤C*(N*rho)^(-(1/2:ℝ))) :
    (∫rho in (0:ℝ)..b,f rho)≤2*C/N := by
  have hbi:=smallInterval_half_intervalIntegrable N b hN hb
  have hae : ∀ᵐrho∂volume.restrict (Icc (0:ℝ) b),f rho≤C*(N*rho)^(-(1/2:ℝ)) := by
    rw [←restrict_Ioo_eq_restrict_Icc]
    exact hbound
  have hh:=intervalIntegral.integral_mono_ae_restrict hb hf (hbi.const_mul C) hae
  rw [intervalIntegral.integral_const_mul,smallInterval_half_integral N b hN hb] at hh
  have hp:=Real.rpow_le_rpow hb hcut (by norm_num : (0:ℝ)≤1/2)
  have he : N^(-(1/2:ℝ))*(1/N)^(1/2:ℝ)=1/N := by
    rw [show (1/N:ℝ)=N⁻¹ by ring,Real.inv_rpow hN.le,←Real.rpow_neg hN.le,
      ←Real.rpow_add hN]
    norm_num [Real.rpow_neg_one]
  calc
    _≤C*(2*N^(-(1/2:ℝ))*b^(1/2:ℝ)):=hh
    _≤C*(2*N^(-(1/2:ℝ))*(1/N)^(1/2:ℝ)):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by positivity)) hC
    _=2*C/N:=by rw [mul_assoc,he];ring

 theorem smallInterval_late_integral_le (N lam eta C b : ℝ) (hN : 1≤N)
    (hlam : 0<lam) (heta : 0≤eta) (hC : 0≤C) (hb1 : b≤1) (hcut : 1/N≤b)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume (1/N) b)
    (hbound : ∀ᵐrho∂volume.restrict (Ioo (1/N:ℝ) b),f rho≤
      C*((Real.log (2+N))^2/(N*rho*lam)+(N*rho)^(-(2/3:ℝ))+
        (N*rho)^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*(smallIntervalOmega rho eta)^(2/3:ℝ))) :
    (∫rho in (1/N:ℝ)..b,f rho)≤C*((Real.log (2+N))^3/(N*lam)+
      3*N^(-(2/3:ℝ))*b^(1/3:ℝ)+
      (9/2:ℝ)*N^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*eta^(1/9:ℝ)*b^(2/9:ℝ)) := by
  have hNp : 0<N:=zero_lt_one.trans_le hN
  have hc : 0<1/N:=by positivity
  have hb : 0≤b:=hc.le.trans hcut
  let g0 : ℝ → ℝ:=fun rho=>((Real.log (2+N))^2/(N*lam))*(1/rho)
  let g1 : ℝ → ℝ:=fun rho=>N^(-(2/3:ℝ))*rho^(-(2/3:ℝ))
  let g2 : ℝ → ℝ:=fun rho=>(N^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*eta^(1/9:ℝ))*rho^(-(7/9:ℝ))
  have hi0 : IntervalIntegrable g0 volume (1/N) b:=
    (smallInterval_reciprocal_intervalIntegrable N b hN hcut).const_mul _
  have hsub : uIcc (1/N:ℝ) b⊆uIcc (0:ℝ) b:=by
    rw [uIcc_of_le hcut,uIcc_of_le hb]
    exact Icc_subset_Icc hc.le le_rfl
  have hi1 : IntervalIntegrable g1 volume (1/N) b:=by
    simpa only [g1,show -(2:ℝ)/3=-(2/3:ℝ) by ring] using
      ((smallInterval_twoThird_intervalIntegrable b).mono_set hsub).const_mul (N^(-(2/3:ℝ)))
  have hi2 : IntervalIntegrable g2 volume (1/N) b:=by
    simpa only [g2,show -(7:ℝ)/9=-(7/9:ℝ) by ring] using
      ((smallInterval_sevenNinth_intervalIntegrable b).mono_set hsub).const_mul
        (N^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*eta^(1/9:ℝ))
  have hiTwo : IntervalIntegrable (fun rho:ℝ=>rho^(-(2/3:ℝ))) volume 0 b := by
    simpa only [show -(2:ℝ)/3=-(2/3:ℝ) by ring] using smallInterval_twoThird_intervalIntegrable b
  have hiSeven : IntervalIntegrable (fun rho:ℝ=>rho^(-(7/9:ℝ))) volume 0 b := by
    simpa only [show -(7:ℝ)/9=-(7/9:ℝ) by ring] using smallInterval_sevenNinth_intervalIntegrable b
  have hae : ∀ᵐrho∂volume.restrict (Icc (1/N:ℝ) b),f rho≤C*(g0 rho+g1 rho+g2 rho) := by
    rw [←restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hbound,ae_restrict_mem measurableSet_Ioo] with rho hr hrho
    exact hr.trans (mul_le_mul_of_nonneg_left
      (smallInterval_pointwise_majorant_le N lam rho eta hNp hlam (hc.trans hrho.1) heta) hC)
  have hh:=intervalIntegral.integral_mono_ae_restrict hcut hf (((hi0.add hi1).add hi2).const_mul C) hae
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (hi0.add hi1) hi2,
    intervalIntegral.integral_add hi0 hi1] at hh
  have he0 : (∫rho in (1/N:ℝ)..b,g0 rho)≤(Real.log (2+N))^3/(N*lam) := by
    dsimp only [g0]
    rw [intervalIntegral.integral_const_mul]
    have hlog:=(smallInterval_reciprocal_integral_le_log N b hN hcut hb1).trans
      (Real.log_le_log hNp (by linarith : N≤2+N))
    have hm:=mul_le_mul_of_nonneg_left hlog
      (by positivity : 0≤(Real.log (2+N))^2/(N*lam))
    convert hm using 1 <;> ring
  have he1 : (∫rho in (1/N:ℝ)..b,g1 rho)≤3*N^(-(2/3:ℝ))*b^(1/3:ℝ) := by
    dsimp only [g1]
    rw [intervalIntegral.integral_const_mul]
    have hm:=intervalIntegral.integral_mono_interval hc.le hcut le_rfl
      (show 0≤ᵐ[volume.restrict (Ioc (0:ℝ) b)] (fun rho:ℝ=>rho^(-(2/3:ℝ))) from by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with rho hrho
        exact Real.rpow_nonneg hrho.1.le _) hiTwo
    have he : (∫rho in (0:ℝ)..b,rho^(-(2/3:ℝ)))=3*b^(1/3:ℝ) := by
      simpa only [show -(2:ℝ)/3=-(2/3:ℝ) by ring] using smallInterval_twoThird_integral b
    rw [he] at hm
    convert mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hNp.le (-(2/3:ℝ))) using 1 <;> ring
  have he2 : (∫rho in (1/N:ℝ)..b,g2 rho)≤
      (9/2:ℝ)*N^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*eta^(1/9:ℝ)*b^(2/9:ℝ) := by
    dsimp only [g2]
    rw [intervalIntegral.integral_const_mul]
    have hm:=intervalIntegral.integral_mono_interval hc.le hcut le_rfl
      (show 0≤ᵐ[volume.restrict (Ioc (0:ℝ) b)] (fun rho:ℝ=>rho^(-(7/9:ℝ))) from by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with rho hrho
        exact Real.rpow_nonneg hrho.1.le _) hiSeven
    have he : (∫rho in (0:ℝ)..b,rho^(-(7/9:ℝ)))=(9/2:ℝ)*b^(2/9:ℝ) := by
      simpa only [show -(7:ℝ)/9=-(7/9:ℝ) by ring] using smallInterval_sevenNinth_integral b
    rw [he] at hm
    convert mul_le_mul_of_nonneg_left hm
      (by positivity : 0≤N^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*eta^(1/9:ℝ)) using 1 <;> ring
  exact hh.trans (mul_le_mul_of_nonneg_left (by linarith only [he0,he1,he2]) hC)

end QuantitativeFollowup
