module
public import FourPapersCommon.RefinedShellPowers

@[expose] public section

/-! A universal refined shell estimate as a genuine consequence of the
stronger logarithmic interval estimate. -/
noncomputable section
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem refined_shell_bound_from_log_window (M m u ell : ℝ)
    (hM : 0<M) (hm : 0<m) (hmu : m≤u) (hell : 0≤ell) :
    512*(min m ((1/(M*u))*(1+max (Real.log (m/(1/(M*u)))) 0))+
      ((1/(M*u))*ell)^(2/3:ℝ)*m^(1/3:ℝ))≤
      2560*(M^(-(3/4:ℝ))*u^(-(1/2:ℝ))+
        M^(-(2/3:ℝ))*u^(-(1/3:ℝ))*ell^(2/3:ℝ)) := by
  have hu : 0<u:=hm.trans_le hmu
  have hε : 0<1/(M*u):=by positivity
  have hfirst : min m ((1/(M*u))*(1+max (Real.log (m/(1/(M*u)))) 0))≤
      5*(M^(-(3/4:ℝ))*u^(-(1/2:ℝ))):=by
    calc
      _≤5*(1/(M*u))*(u/(1/(M*u)))^(1/4:ℝ):=
        min_log_window_le_quarter_power m u (1/(M*u)) hm hmu hε
      _=5*(M^(-(3/4:ℝ))*u^(-(1/2:ℝ))):=by
        rw [mul_assoc,shell_quarter_power_identity M u hM hu]
  have hsecond : ((1/(M*u))*ell)^(2/3:ℝ)*m^(1/3:ℝ)≤
      M^(-(2/3:ℝ))*u^(-(1/3:ℝ))*ell^(2/3:ℝ):=by
    calc
      _≤((1/(M*u))*ell)^(2/3:ℝ)*u^(1/3:ℝ):=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hm.le hmu (by norm_num : (0:ℝ)≤1/3))
          (Real.rpow_nonneg (by positivity) _)
      _=M^(-(2/3:ℝ))*u^(-(1/3:ℝ))*ell^(2/3:ℝ):=
        shell_two_thirds_identity M u ell hM hu hell
  have hnon : 0≤M^(-(2/3:ℝ))*u^(-(1/3:ℝ))*ell^(2/3:ℝ):=by positivity
  linarith

end FourPapersCommon
