module
public import QuantitativeFollowup.SmallIntervalMoving
public import QuantitativeFollowup.DyadicLogOptimization

@[expose] public section

/-! Exact energy-clock cancellation and temperature-only logarithmic
bounds. These are scalar inequalities, with all constants explicit. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000

def smallIntervalLogConstant (β : ℝ) : ℝ := 3+4*Real.log β

theorem smallIntervalLogConstant_pos (β : ℝ) (hβ : 1<β) :
    0<smallIntervalLogConstant β := by
  unfold smallIntervalLogConstant
  linarith [Real.log_pos hβ]

theorem smallInterval_log_bound (N β M : ℝ) (hN : 2 ≤ N) (hβ : 1<β)
    (hM : 0<M) (hMb : M ≤ β^2*N) :
    1+logPlus M ≤ smallIntervalLogConstant β*Real.log (2+N) := by
  have hNp : 0<N:=by linarith
  have hβp : 0<β:=by linarith
  have hln : 0 ≤ Real.log N:=Real.log_nonneg (by linarith)
  have hlβ : 0 ≤ Real.log β:=(Real.log_pos hβ).le
  have hm:=Real.log_le_log hM hMb
  rw [Real.log_mul (sq_pos_of_pos hβp).ne' hNp.ne',Real.log_pow] at hm
  have hplus : logPlus M ≤ 2*Real.log β+Real.log N := by
    unfold logPlus
    exact max_le hm (by linarith)
  have hlogN:=Real.log_le_log hNp (by linarith : N ≤ 2+N)
  have hlog2:=Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : (2:ℝ) ≤ 2+N)
  have hhalf : (1/2:ℝ) ≤ Real.log (2+N):=
    (lt_trans (by norm_num) Real.log_two_gt_d9).le.trans hlog2
  have hprod:=mul_nonneg hlβ (by linarith : 0 ≤ 2*Real.log (2+N)-1)
  unfold smallIntervalLogConstant
  nlinarith

theorem smallInterval_twoThird_normalization (x β : ℝ) (hx : 0<x) (hβ : 0<β) :
    β*(x*β^2)^(-(2/3:ℝ))=β^(-(1/3:ℝ))*x^(-(2/3:ℝ)) := by
  rw [Real.mul_rpow hx.le (sq_nonneg β)]
  have hp : (β^2)^(-(2/3:ℝ))=β^(-(4/3:ℝ)) := by
    rw [←Real.rpow_two,←Real.rpow_mul hβ.le]
    norm_num
  rw [hp]
  calc
    _=(β^(1:ℝ)*β^(-(4/3:ℝ)))*x^(-(2/3:ℝ)):=by rw [Real.rpow_one];ring
    _=_:=by rw [←Real.rpow_add hβ];norm_num

theorem smallInterval_twoThird_le (x β : ℝ) (hx : 0<x) (hβ : 1 ≤ β) :
    β*(x*β^2)^(-(2/3:ℝ)) ≤ x^(-(2/3:ℝ)) := by
  rw [smallInterval_twoThird_normalization x β hx (zero_lt_one.trans_le hβ)]
  apply mul_le_of_le_one_left (Real.rpow_nonneg hx.le _)
  exact Real.rpow_le_one_of_one_le_of_nonpos hβ (by norm_num)

theorem smallInterval_third_normalization (x β lam : ℝ) (hx : 0<x) (hβ : 0<β) (hlam : 0<lam) :
    β*(x*β^2)^(-(2/3:ℝ))*(lam/β)^(-(1/3:ℝ))=
      x^(-(2/3:ℝ))*lam^(-(1/3:ℝ)) := by
  rw [smallInterval_twoThird_normalization x β hx hβ,Real.div_rpow hlam.le hβ.le]
  have hn : β^(-(1/3:ℝ))≠0:=ne_of_gt (Real.rpow_pos_of_pos hβ _)
  field_simp

theorem smallInterval_floor_normalization (x β lam : ℝ) (hx : 0<x) (hβ : 0<β) (hlam : 0<lam) :
    β/((x*β^2)*(lam/β))=1/(x*lam) := by
  field_simp
  <;> ring

end QuantitativeFollowup
