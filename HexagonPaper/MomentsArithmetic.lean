module
public import FourPapersCommon.TruncatedPowerIntegrals
public import FourPapersCommon.ReciprocalBinExclusion

@[expose] public section

/-! Optimized bin constants for the literal 128 variance estimate. -/
noncomputable section
open Set MeasureTheory FourPapersCommon
namespace HexagonPaper
theorem reciprocal_bin_exclusion_32 (psi d ε τ xp xm : ℝ) (hε : 0<ε) (hτ : 0<τ)
    (hxp : 0<xp) (hxm : 0<xm) (hd : d^2≤τ/4)
    (hpsi : τ<psi) (hb : psi≤2*d^2+8*ε*(1/xp+1/xm)) :
    xp≤32*ε/τ ∨ xm≤32*ε/τ := by
  by_contra h
  push_neg at h
  have hδ : 0<32*ε/τ:=by positivity
  have hp : 1/xp≤τ/(32*ε) := by
    have hp:=div_le_div_of_nonneg_left zero_le_one hδ h.1.le
    convert hp using 1 <;> field_simp
  have hm : 1/xm≤τ/(32*ε) := by
    have hm:=div_le_div_of_nonneg_left zero_le_one hδ h.2.le
    convert hm using 1 <;> field_simp
  have hs:=mul_le_mul_of_nonneg_left (add_le_add hp hm) (show 0≤8*ε by positivity)
  have he : 8*ε*(τ/(32*ε)+τ/(32*ε))=τ/2 := by field_simp;ring
  rw [he] at hs
  linarith


theorem truncated_reciprocal_128_bound (h ε : ℝ) (hh : 0<h) (hε : 0<ε) :
    (∫ t : ℝ in Ioo 0 1,min h ((128*ε)/t))≤
      128*min h (ε*(1+max (Real.log (h/ε)) 0)) := by
  have hheight := integral_truncated_reciprocal_le_height h (128*ε) hh (by positivity)
  have hlarge : (∫ t : ℝ in Ioo 0 1,min h ((128*ε)/t))≤128*h := by
    exact hheight.trans (by nlinarith)
  have hlog : (∫ t : ℝ in Ioo 0 1,min h ((128*ε)/t))≤
      128*(ε*(1+max (Real.log (h/ε)) 0)) := by
    rw [integral_truncated_reciprocal h (128*ε) hh (by positivity)]
    split_ifs with hbig
    · have hm := le_max_right (Real.log (h/ε)) 0
      nlinarith
    · have hd : h/(128*ε)≤h/ε :=
        div_le_div_of_nonneg_left hh.le hε (by nlinarith)
      have hl := (Real.log_le_log (by positivity : 0<h/(128*ε)) hd).trans
        (le_max_left (Real.log (h/ε)) 0)
      have hm := mul_le_mul_of_nonneg_left (show 1+Real.log (h/(128*ε))≤
        1+max (Real.log (h/ε)) 0 by linarith) (show 0≤128*ε by positivity)
      nlinarith
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤128)]
  exact le_min hlarge hlog


theorem truncated_three_halves_128_bound (h ε ell : ℝ)
    (hh : 0<h) (hε : 0<ε) (hell : 0≤ell) :
    (∫ t : ℝ in Ioi 0,min h ((128*ε*ell)*t^(-(3/2:ℝ))))≤
      128*(ε*ell)^(2/3:ℝ)*h^(1/3:ℝ) := by
  rw [(integral_truncated_three_halves h (128*ε*ell) hh (by positivity)).2]
  have hk : (128:ℝ)^(2/3:ℝ)≤36 := by
    calc
      (128:ℝ)^(2/3:ℝ)≤((6:ℝ)^3)^(2/3:ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = 36 := by
        rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤6)]
        norm_num
  have he : (128*ε*ell)^(2/3:ℝ)=
      (128:ℝ)^(2/3:ℝ)*(ε*ell)^(2/3:ℝ) := by
    rw [mul_assoc,Real.mul_rpow (by norm_num : (0:ℝ)≤128) (mul_nonneg hε.le hell)]
  rw [he]
  calc
    3*((128:ℝ)^(2/3:ℝ)*(ε*ell)^(2/3:ℝ))*h^(1/3:ℝ)≤
        3*(36*(ε*ell)^(2/3:ℝ))*h^(1/3:ℝ) := by gcongr
    _ ≤ 128*(ε*ell)^(2/3:ℝ)*h^(1/3:ℝ) := by
      nlinarith [mul_nonneg (Real.rpow_nonneg (mul_nonneg hε.le hell) (2/3:ℝ))
        (Real.rpow_nonneg hh.le (1/3:ℝ))]


end HexagonPaper
