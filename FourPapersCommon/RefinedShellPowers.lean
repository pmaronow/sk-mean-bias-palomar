module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! The numerical improvement of the actual quantile interval variance
bound when its interval length is at most the CDF threshold. -/
noncomputable section
open Set
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem min_log_window_le_quarter_power (m u ε : ℝ)
    (hm : 0<m) (hu : m≤u) (hε : 0<ε) :
    min m (ε*(1+max (Real.log (m/ε)) 0))≤5*ε*(u/ε)^(1/4:ℝ) := by
  have hu0 : 0<u:=hm.trans_le hu
  have hz : 0<u/ε:=div_pos hu0 hε
  have hp : 0≤(u/ε)^(1/4:ℝ):=(Real.rpow_pos_of_pos hz _).le
  by_cases hz1 : u/ε≤1
  · have hpower : u/ε≤(u/ε)^(1/4:ℝ):=by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge hz hz1 (by norm_num : (1/4:ℝ)≤1)
    calc
      _≤m:=min_le_left _ _
      _≤u:=hu
      _=ε*(u/ε):=by field_simp <;> ring
      _≤ε*(u/ε)^(1/4:ℝ):=mul_le_mul_of_nonneg_left hpower hε.le
      _≤5*ε*(u/ε)^(1/4:ℝ):=by nlinarith
  · have h1 : 1≤(u/ε)^(1/4:ℝ):=
      Real.one_le_rpow (le_of_not_ge hz1) (by norm_num)
    have hlog : Real.log (m/ε)≤4*(u/ε)^(1/4:ℝ):=by
      have hA:=Real.log_le_log (div_pos hm hε) (div_le_div_of_nonneg_right hu hε.le)
      have hB : Real.log (u/ε)≤4*(u/ε)^(1/4:ℝ):=by
        calc
          _≤(u/ε)^(1/4:ℝ)/(1/4:ℝ):=
            Real.log_le_rpow_div hz.le (by norm_num : (0:ℝ)<1/4)
          _=4*(u/ε)^(1/4:ℝ):=by ring
      linarith
    have hmax : max (Real.log (m/ε)) 0≤4*(u/ε)^(1/4:ℝ):=
      max_le hlog (by positivity)
    calc
      _≤ε*(1+max (Real.log (m/ε)) 0):=min_le_right _ _
      _≤ε*(5*(u/ε)^(1/4:ℝ)):=mul_le_mul_of_nonneg_left (by linarith) hε.le
      _=5*ε*(u/ε)^(1/4:ℝ):=by ring

theorem shell_quarter_power_identity (M u : ℝ) (hM : 0<M) (hu : 0<u) :
    (1/(M*u))*((u/(1/(M*u)))^(1/4:ℝ))=
      M^(-(3/4:ℝ))*u^(-(1/2:ℝ)) := by
  have hz : u/(1/(M*u))=M*u^2:=by field_simp <;> ring
  have hup : (u^2)^(1/4:ℝ)=u^((2:ℝ)*(1/4:ℝ)):=by
    rw [Real.rpow_mul hu.le,Real.rpow_two]
  rw [hz,Real.mul_rpow hM.le (sq_nonneg u),hup]
  have he : (1/(M*u))=M^(-1:ℝ)*u^(-1:ℝ):=by
    rw [Real.rpow_neg_one,Real.rpow_neg_one]
    field_simp
  rw [he]
  calc
    _=(M^(-1:ℝ)*M^(1/4:ℝ))*(u^(-1:ℝ)*u^((2:ℝ)*(1/4:ℝ))):=by ring
    _=M^((-1:ℝ)+(1/4:ℝ))*u^((-1:ℝ)+(2:ℝ)*(1/4:ℝ)):=by
      rw [←Real.rpow_add hM,←Real.rpow_add hu]
    _=M^(-(3/4:ℝ))*u^(-(1/2:ℝ)):=by norm_num

theorem shell_two_thirds_identity (M u ell : ℝ) (hM : 0<M) (hu : 0<u) (hell : 0≤ell) :
    ((1/(M*u))*ell)^(2/3:ℝ)*u^(1/3:ℝ)=
      M^(-(2/3:ℝ))*u^(-(1/3:ℝ))*ell^(2/3:ℝ) := by
  have he : (1/(M*u))=M^(-1:ℝ)*u^(-1:ℝ):=by
    rw [Real.rpow_neg_one,Real.rpow_neg_one]
    field_simp
  rw [he,Real.mul_rpow (by positivity) hell,
    Real.mul_rpow (by positivity) (by positivity),
    ←Real.rpow_mul hM.le,←Real.rpow_mul hu.le]
  calc
    _=M^((-1:ℝ)*(2/3:ℝ))*(u^((-1:ℝ)*(2/3:ℝ))*u^(1/3:ℝ))*ell^(2/3:ℝ):=by ring
    _=M^((-1:ℝ)*(2/3:ℝ))*u^((-1:ℝ)*(2/3:ℝ)+(1/3:ℝ))*ell^(2/3:ℝ):=by
      rw [←Real.rpow_add hu]
    _=M^(-(2/3:ℝ))*u^(-(1/3:ℝ))*ell^(2/3:ℝ):=by norm_num

end FourPapersCommon
