module
public import QuantitativeFollowup.ScalarRootGrowth
public import QuantitativeFollowup.RegularizedTrialGeometry
public import FourPapersCommon.CDFDistanceTriangle

@[expose] public section

/-! The actual clipped scalar trial differs from the scalar minimizer by
quadratic order in its prescribed root mass. The estimate uses the genuine
positive scalar root density and the exact clipping CDF, including atoms. -/
noncomputable section
open Set MeasureTheory Paper FRSB
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000

theorem scalarClippedTrialMeasure_distance_of_root_growth
    (beta : ℝ) (hb : 0<beta) (μ : Paper.ParisiMeasure)
    (k T : ℝ) (hk : 0<k) (hT : T∈Ioo (0 : ℝ) 1)
    (hg : ∀r∈Icc (0 : ℝ) T,k*r≤beta*parisiCDF μ r)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) beta) :
    beta*parisiCDFDistance μ
      (scalarClippedTrialMeasure (lam/beta)
        ⟨div_nonneg hlam.1 hb.le,(div_le_one hb).mpr hlam.2⟩ μ)
      ≤(1/(k*T))*lam^2 := by
  let hs : lam/beta∈Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hlam.1 hb.le,(div_le_one hb).mpr hlam.2⟩
  let ν := scalarClippedTrialMeasure (lam/beta) hs μ
  let f := fun x : ℝ=>beta*|parisiCDF μ x-parisiCDF ν x|
  have hi (a b : ℝ) : IntervalIntegrable f volume a b :=
    (parisiCDF_abs_diff_intervalIntegrable μ ν a b).const_mul beta
  have hf (x : ℝ) (hx : x∈Icc (0 : ℝ) 1) :
      f x=max lam (beta*parisiCDF μ x)-beta*parisiCDF μ x := by
    have hroot : beta*(lam/beta)=lam := by field_simp
    have hclip := scalarClippedTrialMeasure_energy_cdf beta hb.le μ (lam/beta) hs x hx
    simp only [scalarTrialProfile,hroot] at hclip
    have hCDF := scalarClippedTrialMeasure_cdf (lam/beta) hs μ x hx
    have hle : parisiCDF μ x≤parisiCDF ν x := by
      change parisiCDF μ x≤parisiCDF (scalarClippedTrialMeasure (lam/beta) hs μ) x
      rw [hCDF]
      exact le_max_right _ _
    change beta*|parisiCDF μ x-parisiCDF ν x|=_
    rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hle),mul_sub]
    change beta*parisiCDF (scalarClippedTrialMeasure (lam/beta) hs μ) x-_= _
    rw [hclip]
  have hbound : ∀x∈Icc (0 : ℝ) 1,f x≤lam := by
    intro x hx
    rw [hf x hx]
    have hnonneg := mul_nonneg hb.le (parisiCDF_nonneg μ x)
    exact sub_le_iff_le_add.mpr (max_le (by linarith) (by linarith only [hlam.1]))
  have he : beta*parisiCDFDistance μ ν=∫x in (0 : ℝ)..1,f x := by
    rw [parisiCDFDistance,←intervalIntegral.integral_const_mul]
  change beta*parisiCDFDistance μ ν≤_
  rw [he]
  have hkT : 0<k*T := mul_pos hk hT.1
  by_cases hsmall : lam≤k*T
  · let R := lam/k
    have hR0 : 0≤R := div_nonneg hlam.1 hk.le
    have hRT : R≤T := (div_le_iff₀ hk).mpr (by nlinarith only [hsmall])
    have hR1 : R≤1 := hRT.trans hT.2.le
    have hrootR : lam≤beta*parisiCDF μ R := by
      have hkr : k*R=lam := by dsimp only [R]; field_simp
      simpa only [hkr] using hg R ⟨hR0,hRT⟩
    have hzero : (∫x in R..(1 : ℝ),f x)=0 := by
      have hz : EqOn f (fun _=> (0 : ℝ)) (uIcc R 1) := by
        intro x hx
        rw [uIcc_of_le hR1] at hx
        rw [hf x ⟨hR0.trans hx.1,hx.2⟩]
        have hm := mul_le_mul_of_nonneg_left (parisiCDF_monotone μ hx.1) hb.le
        rw [max_eq_right (hrootR.trans hm),sub_self]
      rw [intervalIntegral.integral_congr hz]
      simp
    have hshort : (∫x in (0 : ℝ)..R,f x)≤lam*R := by
      have hh := intervalIntegral.integral_mono_on hR0 (hi 0 R)
        (intervalIntegrable_const (c:=lam))
        (fun x hx=>hbound x ⟨hx.1,hx.2.trans hR1⟩)
      simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm] using hh
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hi 0 R) (hi R 1)
    rw [hzero,add_zero] at hadd
    rw [←hadd]
    apply hshort.trans
    have hscale : k*T≤k := by nlinarith only [hT.2.le,hk.le]
    have hrec : 1/k≤1/(k*T) := one_div_le_one_div_of_le hkT hscale
    have hm := mul_le_mul_of_nonneg_right hrec (sq_nonneg lam)
    have heq : lam*R=(1/k)*lam^2 := by dsimp only [R]; ring
    rw [heq]
    exact hm
  · have hh := intervalIntegral.integral_mono_on (show (0 : ℝ)≤1 by norm_num)
      (hi 0 1) (intervalIntegrable_const (c:=lam)) hbound
    have hfull : (∫x in (0 : ℝ)..1,f x)≤lam := by
      simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using hh
    apply hfull.trans
    have hl : k*T≤lam := (lt_of_not_ge hsmall).le
    calc
      lam≤lam^2/(k*T) := (le_div_iff₀ hkT).mpr (by nlinarith only [hl,hlam.1])
      _=(1/(k*T))*lam^2 := by ring

theorem scalar_clipped_distance (beta : ℝ) (hbeta : 1<beta) :
    ∃C : ℝ,0<C ∧ ∀μ : Paper.ParisiMeasure,
      IsParisiMinimizer beta 0 μ→∀lam : ℝ,∀hlam : lam∈Icc (0 : ℝ) beta,
      beta*parisiCDFDistance μ
        (scalarClippedTrialMeasure (lam/beta)
          ⟨div_nonneg hlam.1 (zero_lt_one.trans hbeta).le,
            (div_le_one (zero_lt_one.trans hbeta)).mpr hlam.2⟩ μ)≤C*lam^2 := by
  obtain ⟨k,T,hk,hT,hg⟩ := scalar_root_growth_uniform_minimizers beta hbeta
  refine ⟨1/(k*T),one_div_pos.mpr (mul_pos hk hT.1),?_⟩
  intro μ hμ lam hlam
  exact scalarClippedTrialMeasure_distance_of_root_growth beta (zero_lt_one.trans hbeta)
    μ k T hk hT (hg μ hμ) lam hlam

end QuantitativeFollowup
