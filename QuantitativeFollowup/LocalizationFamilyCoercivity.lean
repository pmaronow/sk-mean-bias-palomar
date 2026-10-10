module
public import QuantitativeFollowup.LocalizationMassSelection
public import QuantitativeFollowup.LocalizationInteriorFamilies
public import QuantitativeFollowup.LocalizationBoundaryCutoffs
public import Mathlib.Tactic

@[expose] public section

/-! Exact smooth-family coefficients for the isolation argument. The
common geometric family has genuine area and energy; no limiting
functional derivative is assumed by this deterministic calculation. -/
noncomputable section
open Set MeasureTheory FourPapersCommon
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000

def smoothLocalizationConstant (beta L k : ℝ) : ℝ :=
  (1/144)*min (105*k^4/(32768*beta*L^2)) (k^2/(4*beta))

theorem smoothLocalizationConstant_pos (beta L k : ℝ)
    (hb : 0<beta) (hL : 0<L) (hk : 0<k) :
    0<smoothLocalizationConstant beta L k := by
  unfold smoothLocalizationConstant
  positivity

def smoothFamilyCoefficient (beta rho h k A N ell : ℝ) : ℝ :=
  rho*A^2/72*min ((rho*k^2*N*ell/2)^2/(beta*N*512/(105*ell)))
    ((rho*k^2*N*ell/2)/(2*beta/h))

theorem smoothFamilyCoefficient_eq (beta rho h k A N ell : ℝ)
    (hb : 0<beta) (hr : 0≤rho) (hh : 0<h) (hN : 0<N) (he : 0<ell) :
    smoothFamilyCoefficient beta rho h k A N ell =
      rho^2*A^2*N*ell/72*min (105*rho*k^4*ell^2/(2048*beta)) (k^2*h/(4*beta)) := by
  unfold smoothFamilyCoefficient
  have h1 : (rho*k^2*N*ell/2)^2/(beta*N*512/(105*ell))=
      N*ell*rho*(105*rho*k^4*ell^2/(2048*beta)) := by
    field_simp
    ring
  have h2 : (rho*k^2*N*ell/2)/(2*beta/h)=N*ell*rho*(k^2*h/(4*beta)) := by
    field_simp
    ring
  rw [h1,h2,←mul_min_of_nonneg _ _ (mul_nonneg (mul_pos hN he).le hr)]
  ring

theorem smoothFamilyCoefficient_interior_lower (beta L k rho h A N : ℝ)
    (hb : 0<beta) (hL : 0<L) (hk : 0≤k) (hr : 0<rho) (hh : 0<h)
    (hA : 0<A) (hN : 0<N) :
    smoothLocalizationConstant beta L k*rho^2*A^2*N*(A/(4*L))*min (rho*A^2) h ≤
      smoothFamilyCoefficient beta rho h k A N (A/(4*L)) := by
  let c := min (105*k^4/(32768*beta*L^2)) (k^2/(4*beta))
  have hc : 0≤c := le_min (by positivity) (by positivity)
  have hmin : c*min (rho*A^2) h ≤
      min (105*rho*k^4*(A/(4*L))^2/(2048*beta)) (k^2*h/(4*beta)) := by
    rw [mul_min_of_nonneg _ _ hc]
    apply min_le_min
    · have hh := mul_le_mul_of_nonneg_right (min_le_left (105*k^4/(32768*beta*L^2))
        (k^2/(4*beta))) (mul_nonneg hr.le (sq_nonneg A))
      convert hh using 1
      field_simp
      ring
    · have hh := mul_le_mul_of_nonneg_right (min_le_right (105*k^4/(32768*beta*L^2))
        (k^2/(4*beta))) hh.le
      convert hh using 1
      ring
  rw [smoothFamilyCoefficient_eq beta rho h k A N (A/(4*L)) hb hr.le hh hN (by positivity)]
  have hm := mul_le_mul_of_nonneg_left hmin
    (by positivity : 0≤rho^2*A^2*N*(A/(4*L))/72)
  have hm0 : 0≤c*min (rho*A^2) h := mul_nonneg hc (le_min (by positivity) hh.le)
  have hscale : rho^2*A^2*N*(A/(4*L))/144 ≤ rho^2*A^2*N*(A/(4*L))/72 := by
    have hprod : 0≤rho^2*A^2*N*(A/(4*L)) := by positivity
    linarith
  have hlo := mul_le_mul_of_nonneg_right hscale hm0
  refine (le_trans ?_ (hlo.trans hm))
  dsimp only [smoothLocalizationConstant,c]
  ring_nf
  rfl

theorem smoothFamilyCoefficient_boundary_lower (beta L k rho h A w : ℝ)
    (hb : 0<beta) (hL : 1≤L) (hk : 0≤k) (hr : 0<rho) (hh : 0<h)
    (hA : 0<A) (hw : 0<w) :
    smoothLocalizationConstant beta L k*rho^2*A^2*w*min (rho*w^2) h ≤
      smoothFamilyCoefficient beta rho h k A 1 (w/2) := by
  let c := min (105*k^4/(32768*beta*L^2)) (k^2/(4*beta))
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hc : 0≤c := le_min (by positivity) (by positivity)
  have hfirst : c ≤ 105*k^4/(8192*beta) := by
    refine (min_le_left _ _).trans ?_
    apply (div_le_div_iff₀ (by positivity : 0<32768*beta*L^2)
      (by positivity : 0<8192*beta)).mpr
    have hL2 : 1≤L^2 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hb.le (pow_nonneg hk 4)) (sub_nonneg.mpr hL2),
      mul_nonneg hb.le (pow_nonneg hk 4)]
  have hmin : c*min (rho*w^2) h ≤
      min (105*rho*k^4*(w/2)^2/(2048*beta)) (k^2*h/(4*beta)) := by
    rw [mul_min_of_nonneg _ _ hc]
    apply min_le_min
    · have hm := mul_le_mul_of_nonneg_right hfirst (mul_nonneg hr.le (sq_nonneg w))
      convert hm using 1
      ring
    · have hm := mul_le_mul_of_nonneg_right (min_le_right (105*k^4/(32768*beta*L^2))
        (k^2/(4*beta))) hh.le
      convert hm using 1
      ring
  rw [smoothFamilyCoefficient_eq beta rho h k A 1 (w/2) hb hr.le hh (by norm_num) (half_pos hw)]
  have hm := mul_le_mul_of_nonneg_left hmin
    (by positivity : 0≤rho^2*A^2*1*(w/2)/72)
  convert hm using 1
  dsimp only [smoothLocalizationConstant,c]
  ring

end QuantitativeFollowup
