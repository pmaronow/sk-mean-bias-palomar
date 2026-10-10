module
public import QuantitativePaper.UniformBoundaryBarrier

@[expose] public section

/-! Genuine values of the explicit barrier on every parabolic boundary face. -/
noncomputable section
open Set
namespace QuantitativePaper

theorem uniformBoundaryBarrier_nonpos_of_phase (τ ell ε : ℝ) (p : ℝ×ℝ)
    (hτ : 0<τ) (hε : 0≤ε) (hp : uniformBoundaryPhase τ ell p≤0) :
    uniformBoundaryBarrier τ ell ε p≤0 := by
  have hα : 0≤uniformBoundaryAlpha τ:=(div_pos (by norm_num : (0 : ℝ)<32) hτ).le
  have he : Real.exp (uniformBoundaryAlpha τ*uniformBoundaryPhase τ ell p)≤1:=by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos hα hp)
  unfold uniformBoundaryBarrier
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hε (Real.exp_pos _).le) (by linarith)

theorem uniformBoundaryBarrier_initial_nonpos (τ ell ε x : ℝ)
    (hτ : 0<τ) (hell : 0<ell) (hε : 0≤ε) (hx : x≤ell) :
    uniformBoundaryBarrier τ ell ε (0,x)≤0 := by
  apply uniformBoundaryBarrier_nonpos_of_phase τ ell ε (0,x) hτ hε
  have hh : x/ell≤1:=(div_le_iff₀ hell).mpr (by simpa only [one_mul] using hx)
  simpa only [uniformBoundaryPhase,sub_zero,div_self hτ.ne'] using sub_nonpos.mpr hh

theorem uniformBoundaryBarrier_left_nonpos (τ ell ε r : ℝ)
    (hτ : 0<τ) (hε : 0≤ε) (hr : r≤τ) :
    uniformBoundaryBarrier τ ell ε (r,0)≤0 := by
  apply uniformBoundaryBarrier_nonpos_of_phase τ ell ε (r,0) hτ hε
  simp only [uniformBoundaryPhase,zero_div,zero_sub]
  exact neg_nonpos.mpr (div_nonneg (sub_nonneg.mpr hr) hτ.le)

theorem uniformBoundaryBarrier_right_le (τ ell ε r : ℝ)
    (hτ : 0<τ) (hell : 0<ell) (hε : 0≤ε) (hr : r≤τ) :
    uniformBoundaryBarrier τ ell ε (r,ell)≤ε := by
  have hα : 0≤uniformBoundaryAlpha τ:=(div_pos (by norm_num : (0 : ℝ)<32) hτ).le
  have hp : uniformBoundaryPhase τ ell (r,ell)≤1:=by
    simp only [uniformBoundaryPhase,div_self hell.ne']
    linarith [div_nonneg (sub_nonneg.mpr hr) hτ.le]
  have he : Real.exp (uniformBoundaryAlpha τ*uniformBoundaryPhase τ ell (r,ell))≤
      Real.exp (uniformBoundaryAlpha τ):=
    Real.exp_le_exp.mpr (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hα)
  calc
    _≤ε*Real.exp (-uniformBoundaryAlpha τ)*Real.exp (uniformBoundaryAlpha τ):=by
      unfold uniformBoundaryBarrier
      exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hε (Real.exp_pos _).le)
    _=ε:=by rw [mul_assoc,←Real.exp_add];simp

end QuantitativePaper
