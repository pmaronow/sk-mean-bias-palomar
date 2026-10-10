module
public import QuantitativeFollowup.SmallIntervalOptimized
public import FourPapersCommon.SmallIntervalPowerIntegration

@[expose] public section

/-! Genuine positive-clock factorization and integrable small-interval
power majorants. No profile or defect estimate is assumed here. -/
noncomputable section
open Set MeasureTheory FourPapersCommon
namespace QuantitativeFollowup
set_option maxHeartbeats 2000000

 theorem smallInterval_omega_power_le (rho eta : ℝ) (hrho : 0<rho) (heta : 0≤eta) :
    rho^(-(2/3:ℝ))*(smallIntervalOmega rho eta)^(2/3:ℝ) ≤
      eta^(1/9:ℝ)*rho^(-(7/9:ℝ)) := by
  have homega:=smallIntervalOmega_nonneg rho eta hrho.le heta
  have hh:=Real.rpow_le_rpow homega (min_le_right (1:ℝ) ((eta/rho)^(1/6:ℝ))) (by norm_num : (0:ℝ)≤2/3)
  change (smallIntervalOmega rho eta)^(2/3:ℝ) ≤ _ at hh
  rw [←Real.rpow_mul (div_nonneg heta hrho.le)] at hh
  norm_num at hh
  have he : rho^(-(2/3:ℝ))*(eta/rho)^(1/9:ℝ)=eta^(1/9:ℝ)*rho^(-(7/9:ℝ)) := by
    have hd : (eta/rho)^(1/9:ℝ)=eta^(1/9:ℝ)*rho^(-(1/9:ℝ)) := by
      rw [Real.div_rpow heta hrho.le,Real.rpow_neg hrho.le]
      rfl
    rw [hd]
    calc
      _=eta^(1/9:ℝ)*(rho^(-(2/3:ℝ))*rho^(-(1/9:ℝ))):=by ring
      _=_:=by rw [←Real.rpow_add hrho];norm_num
  exact (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hrho.le _)).trans_eq he

 theorem smallInterval_pointwise_majorant_le (N lam rho eta : ℝ)
    (hN : 0<N) (hlam : 0<lam) (hrho : 0<rho) (heta : 0≤eta) :
    (Real.log (2+N))^2/(N*rho*lam)+(N*rho)^(-(2/3:ℝ))+
      (N*rho)^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*(smallIntervalOmega rho eta)^(2/3:ℝ) ≤
    ((Real.log (2+N))^2/(N*lam))*(1/rho)+N^(-(2/3:ℝ))*rho^(-(2/3:ℝ))+
      (N^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*eta^(1/9:ℝ))*rho^(-(7/9:ℝ)) := by
  rw [Real.mul_rpow hN.le hrho.le]
  have hh:=mul_le_mul_of_nonneg_left (smallInterval_omega_power_le rho eta hrho heta)
    (by positivity : 0≤N^(-(2/3:ℝ))*lam^(-(1/3:ℝ)))
  have he : (Real.log (2+N))^2/(N*rho*lam)=((Real.log (2+N))^2/(N*lam))*(1/rho) := by ring
  rw [he]
  have ht:=add_le_add_left hh (((Real.log (2+N))^2/(N*lam))*(1/rho)+N^(-(2/3:ℝ))*rho^(-(2/3:ℝ)))
  convert ht using 1 <;> ring

 theorem smallInterval_half_integral (N b : ℝ) (hN : 0<N) (hb : 0≤b) :
    (∫rho in (0:ℝ)..b,(N*rho)^(-(1/2:ℝ)))=2*N^(-(1/2:ℝ))*b^(1/2:ℝ) := by
  have hi : IntervalIntegrable (fun rho:ℝ=>rho^(-(1/2:ℝ))) volume 0 b:=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have he : (∫rho in (0:ℝ)..b,(N*rho)^(-(1/2:ℝ)))=
      N^(-(1/2:ℝ))*(∫rho in (0:ℝ)..b,rho^(-(1/2:ℝ))) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with rho
    intro hrho
    have hp : 0≤rho:=(by simpa only [uIoc_of_le hb] using hrho : rho∈Ioc (0:ℝ) b).1.le
    exact Real.mul_rpow hN.le hp
  rw [he,integral_rpow (Or.inl (by norm_num))]
  norm_num
  ring

 theorem smallInterval_half_intervalIntegrable (N b : ℝ) (hN : 0<N) (hb : 0≤b) :
    IntervalIntegrable (fun rho:ℝ=>(N*rho)^(-(1/2:ℝ))) volume 0 b := by
  have hi : IntervalIntegrable (fun rho:ℝ=>rho^(-(1/2:ℝ))) volume 0 b:=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hh:=hi.const_mul (N^(-(1/2:ℝ)))
  apply hh.congr
  intro rho hrho
  have hp : 0≤rho:=(by simpa only [uIoc_of_le hb] using hrho : rho∈Ioc (0:ℝ) b).1.le
  exact (Real.mul_rpow hN.le hp).symm

end QuantitativeFollowup
