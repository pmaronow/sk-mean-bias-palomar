module
public import FourPapersCommon.RefinedShellPowers

@[expose] public section

/-! Genuine power identities and bounds used by the moving cutoff. -/
noncomputable section
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem shell_power_ratio (M u a b r : ℝ) (hM : 0<M) (hu : 0<u) :
    M^a*u^b*(M*u^2)^r=M^(a+r)*u^(b+2*r) := by
  have hup : (u^2)^r=u^((2:ℝ)*r):=by
    rw [Real.rpow_mul hu.le,Real.rpow_two]
  rw [Real.mul_rpow hM.le (sq_nonneg u),hup]
  calc
    _=(M^a*M^r)*(u^b*u^(2*r)):=by ring
    _=M^(a+r)*u^(b+2*r):=by rw [←Real.rpow_add hM,←Real.rpow_add hu]

theorem moving_shell_quarter_dominance (M u : ℝ) (hM : 0<M) (hu : 0<u)
    (hMu : 1≤M*u^2) :
    M^(-(3/4:ℝ))*u^(-(1/2:ℝ))≤M^(-(2/3:ℝ))*u^(-(1/3:ℝ)) := by
  have he : M^(-(2/3:ℝ))*u^(-(1/3:ℝ))*(M*u^2)^(-(1/12:ℝ))=
      M^(-(3/4:ℝ))*u^(-(1/2:ℝ)):=by
    rw [shell_power_ratio M u _ _ _ hM hu]
    norm_num
  rw [←he]
  have hpow:=Real.rpow_le_one_of_one_le_of_nonpos hMu (by norm_num : -(1/12:ℝ)≤0)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow
    (by positivity : 0≤M^(-(2/3:ℝ))*u^(-(1/3:ℝ)))

theorem moving_shell_reciprocal_dominance (M u : ℝ) (hM : 0<M) (hu : 0<u)
    (hMu : 1≤M*u^2) : 1/(M*u)≤M^(-(2/3:ℝ))*u^(-(1/3:ℝ)) := by
  have he : M^(-(2/3:ℝ))*u^(-(1/3:ℝ))*(M*u^2)^(-(1/3:ℝ))=1/(M*u):=by
    rw [shell_power_ratio M u _ _ _ hM hu]
    norm_num
    rw [Real.rpow_neg_one,Real.rpow_neg_one]
    field_simp
  rw [←he]
  have hpow:=Real.rpow_le_one_of_one_le_of_nonpos hMu (by norm_num : -(1/3:ℝ)≤0)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow
    (by positivity : 0≤M^(-(2/3:ℝ))*u^(-(1/3:ℝ)))

theorem dyadic_shell_power_identity (M u : ℝ) (hM : 0<M) (hu : 0<u) (j : ℕ) :
    M^(-(2/3:ℝ))*((2:ℝ)^j*u)^(-(1/3:ℝ))=
      (M^(-(2/3:ℝ))*u^(-(1/3:ℝ)))*((2:ℝ)^(-(1/3:ℝ)))^j := by
  have hpow : ((2:ℝ)^j)^(-(1/3:ℝ))=((2:ℝ)^(-(1/3:ℝ)))^j:=by
    rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2)]
    rw [mul_comm (j:ℝ) (-(1/3:ℝ)),Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  rw [Real.mul_rpow (by positivity) hu.le,hpow]
  ring

end FourPapersCommon
