module
public import QuantitativeFollowup.LocalizationCaseCombination

@[expose] public section

/-! The genuine four-piece selection in localization. The piece masses
are the actual layer-cake integrals, rather than abstract nonnegative
numbers supplied to the selection argument. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

def localizationPieceIntegral (psi : ℝ → ℝ) (q L : ℝ) (j : Fin 4) : ℝ :=
  ∫ A : ℝ in Ioi 0, localizationLevelMass psi q L A j

theorem localizationPieceIntegral_nonneg (psi : ℝ → ℝ) (q L : ℝ) (j : Fin 4) :
    0 ≤ localizationPieceIntegral psi q L j := by
  exact integral_nonneg fun _ => measureReal_nonneg

theorem localizationPieceIntegral_sum (psi : ℝ → ℝ) (hpsi : Measurable psi)
    (q L beta : ℝ) (hq : q∈Ioo (0 : ℝ) 1) (hL : 0<L) (hbeta : 0<beta)
    (hbound : ∀x∈Icc (0 : ℝ) 1, |psi x|≤beta)
    (hpost : ∀x∈Icc q 1, 0≤psi x) :
    (∑j : Fin 4, localizationPieceIntegral psi q L j) =
      ∫x in (0 : ℝ)..1, |psi x| := by
  exact (localization_layercake psi hpsi q L beta hq hL hbeta hbound hpost).symm

theorem localizationPieceIntegral_le_beta (psi : ℝ → ℝ) (hpsi : Measurable psi)
    (q L beta : ℝ) (hq : q∈Ioo (0 : ℝ) 1) (hL : 0<L) (hbeta : 0<beta)
    (hbound : ∀x∈Icc (0 : ℝ) 1, |psi x|≤beta)
    (hpost : ∀x∈Icc q 1, 0≤psi x) (j : Fin 4) :
    localizationPieceIntegral psi q L j ≤ beta := by
  have hsum : localizationPieceIntegral psi q L j ≤
      ∑i : Fin 4, localizationPieceIntegral psi q L i :=
    Finset.single_le_sum (fun i _ => localizationPieceIntegral_nonneg psi q L i)
      (Finset.mem_univ j)
  rw [localizationPieceIntegral_sum psi hpsi q L beta hq hL hbeta hbound hpost] at hsum
  have hi : IntervalIntegrable (fun x => |psi x|) volume 0 1 := by
    apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => beta) volume 0 1).mono_fun
      hpsi.norm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [uIoc_of_le zero_le_one] at hx
    simpa only [Real.norm_eq_abs, abs_abs, abs_of_pos hbeta] using
      hbound x ⟨hx.1.le,hx.2⟩
  have hb := intervalIntegral.integral_mono_on zero_le_one hi intervalIntegrable_const hbound
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hsum.trans hb

theorem exists_large_localizationPieceIntegral (psi : ℝ → ℝ) (hpsi : Measurable psi)
    (q L beta D : ℝ) (hq : q∈Ioo (0 : ℝ) 1) (hL : 0<L) (hbeta : 0<beta)
    (hbound : ∀x∈Icc (0 : ℝ) 1, |psi x|≤beta)
    (hpost : ∀x∈Icc q 1, 0≤psi x)
    (hbudget : D/2 ≤ ∫x in (0 : ℝ)..1, |psi x|) :
    ∃j : Fin 4, D/8 ≤ localizationPieceIntegral psi q L j := by
  by_contra h
  push Not at h
  have hs := localizationPieceIntegral_sum psi hpsi q L beta hq hL hbeta hbound hpost
  have hstrict : (∑j : Fin 4, localizationPieceIntegral psi q L j) <
      ∑_j : Fin 4, D/8 :=
    Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun j _ => h j)
  norm_num at hstrict
  linarith

theorem localization_curvature_bound_of_piece_cases (psi : ℝ → ℝ) (hpsi : Measurable psi)
    (q L beta D K rho h : ℝ) (hq : q∈Ioo (0 : ℝ) 1) (hL : 0<L) (hbeta : 0<beta)
    (hD : 0≤D) (hK : 0≤K) (hrho : 0<rho) (hh : 0<h)
    (hbound : ∀x∈Icc (0 : ℝ) 1, |psi x|≤beta)
    (hpost : ∀x∈Icc q 1, 0≤psi x)
    (hbudget : D/2 ≤ ∫x in (0 : ℝ)..1, |psi x|)
    (hcases : ∀j : Fin 4,
      localizationPieceIntegral psi q L j ≤ (4/3 : ℝ)*(K/rho)^((1 : ℝ)/4)+2*Real.sqrt (K/h) ∨
      localizationPieceIntegral psi q L j ≤ 3*beta^((1 : ℝ)/3)*(K/rho)^((1 : ℝ)/3)+
        3*(K/h)^((2/3 : ℝ))/(2*(2*L)^((1 : ℝ)/3)) ∨
      localizationPieceIntegral psi q L j ≤ 3*beta^((1 : ℝ)/3)*(K/rho)^((1 : ℝ)/3)+2*Real.sqrt (K/h)) :
    (1/8 : ℝ)^4 * localizationCaseConstant beta L * min (rho*D^4) (h*D^2) ≤ K := by
  obtain ⟨j,hj⟩ := exists_large_localizationPieceIntegral psi hpsi q L beta D hq hL hbeta hbound hpost hbudget
  have hm := localization_case_combination (localizationPieceIntegral psi q L j) K rho h beta L
    (localizationPieceIntegral_nonneg psi q L j)
    (localizationPieceIntegral_le_beta psi hpsi q L beta hq hL hbeta hbound hpost j)
    hK hrho hh hbeta hL (hcases j)
  have hpow4 := pow_le_pow_left₀ (by positivity : 0≤D/8) hj 4
  have hpow2 := pow_le_pow_left₀ (by positivity : 0≤D/8) hj 2
  have hmin : (1/8 : ℝ)^4*min (rho*D^4) (h*D^2) ≤
      min (rho*(localizationPieceIntegral psi q L j)^4) (h*(localizationPieceIntegral psi q L j)^2) := by
    rw [mul_min_of_nonneg _ _ (by positivity)]
    apply min_le_min
    · have hh4 := mul_le_mul_of_nonneg_left hpow4 hrho.le
      nlinarith
    · have hh2 := mul_le_mul_of_nonneg_left hpow2 hh.le
      nlinarith
  have hh' := mul_le_mul_of_nonneg_left hmin (localizationCaseConstant_pos beta L hbeta hL).le
  have hh'' : (1/8 : ℝ)^4 * localizationCaseConstant beta L * min (rho*D^4) (h*D^2) ≤
      localizationCaseConstant beta L *
        min (rho*(localizationPieceIntegral psi q L j)^4) (h*(localizationPieceIntegral psi q L j)^2) := by
    convert hh' using 1
    ring
  exact hh''.trans hm

end QuantitativeFollowup
