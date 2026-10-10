module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! Exact boundary-strip constants for the quantile-bin second-moment
estimate.  This is elementary arithmetic, separate from its actual-law
instantiation. -/
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem reciprocal_bin_exclusion (psi d ε τ xp xm : ℝ) (hε : 0<ε) (hτ : 0<τ)
    (hxp : 0<xp) (hxm : 0<xm) (hd : d^2≤τ/64)
    (hpsi : τ<psi) (hb : psi≤2*d^2+8*ε*(1/xp+1/xm)) :
    xp≤64*ε/τ ∨ xm≤64*ε/τ := by
  by_contra h
  push_neg at h
  have hδ : 0<64*ε/τ:=by positivity
  have hp : 1/xp≤τ/(64*ε) := by
    have hp:=div_le_div_of_nonneg_left zero_le_one hδ h.1.le
    convert hp using 1 <;> field_simp
  have hm : 1/xm≤τ/(64*ε) := by
    have hm:=div_le_div_of_nonneg_left zero_le_one hδ h.2.le
    convert hm using 1 <;> field_simp
  have hs:=mul_le_mul_of_nonneg_left (add_le_add hp hm) (show 0≤8*ε by positivity)
  have he : 8*ε*(τ/(64*ε)+τ/(64*ε))=τ/4 := by field_simp;ring
  rw [he] at hs
  linarith

theorem sqrt_bin_width_square (τ : ℝ) (hτ : 0≤τ) : (Real.sqrt τ/8)^2=τ/64 := by
  rw [div_pow,Real.sq_sqrt hτ]
  norm_num

end FourPapersCommon
