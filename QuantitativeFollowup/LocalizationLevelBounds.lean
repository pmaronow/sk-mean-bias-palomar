module
public import QuantitativeFollowup.LocalizationLayercake
public import FourPapersCommon.InversePowerLayercake
public import FourPapersCommon.LinearInverseSquareIntegral

@[expose] public section

/-! Pointwise and integrated level-set bounds from the explicit cutoff
curvature estimates. The estimates are analytic inputs here; measurability,
layer-cake mass, power integrals and all constants are genuine. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000

theorem interior_level_bound (m K rho h A : ℝ)
    (_hm : 0≤m) (hm1 : m≤1) (hK : 0≤K) (hrho : 0<rho) (hh : 0<h) (hA : 0<A)
    (hcurvature : A^2*m*min (rho*A^2) h ≤ K) :
    m ≤ min 1 ((K/rho)*A^(-(4 : ℝ))) + min 1 ((K/h)*A^(-(2 : ℝ))) := by
  have he₄ : (K/rho)*A^(-(4 : ℝ)) = K/(rho*A^4) := by
    rw [Real.rpow_neg hA.le, show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
    field_simp
  have he₂ : (K/h)*A^(-(2 : ℝ)) = K/(h*A^2) := by
    rw [Real.rpow_neg hA.le, Real.rpow_two]
    field_simp
  rw [he₄,he₂]
  have hpos4 : 0<rho*A^4 := by positivity
  have hpos2 : 0<h*A^2 := by positivity
  by_cases hcase : rho*A^2≤h
  · rw [min_eq_left hcase] at hcurvature
    have hb : m≤K/(rho*A^4) := (le_div_iff₀ hpos4).mpr (by nlinarith)
    exact (le_min hm1 hb).trans (le_add_of_nonneg_right (le_min zero_le_one (by positivity)))
  · rw [min_eq_right (le_of_not_ge hcase)] at hcurvature
    have hb : m≤K/(h*A^2) := (le_div_iff₀ hpos2).mpr (by nlinarith)
    exact (le_min hm1 hb).trans (le_add_of_nonneg_left (le_min zero_le_one (by positivity)))

/-- Literal cubic boundary-width bound. The small-width estimate is
preserved in the second term rather than thrown away. -/
theorem boundary_level_bound (m w cap K rho h A : ℝ)
    (_hm : 0≤m) (hw : 0≤w) (hcap : 0≤cap) (hmw : m≤w) (hmcap : m≤cap)
    (hK : 0≤K) (hrho : 0<rho) (hh : 0<h) (hA : 0<A)
    (hcurvature : A^2*w*min (rho*w^2) h ≤ K) :
    m ≤ (K/(rho*A^2))^((1 : ℝ)/3) + min cap (K/(h*A^2)) := by
  have hden : 0<rho*A^2 := by positivity
  have hroot0 : 0≤(K/(rho*A^2))^((1 : ℝ)/3) := Real.rpow_nonneg (by positivity) _
  by_cases hcase : rho*w^2≤h
  · rw [min_eq_left hcase] at hcurvature
    have hp : w^3≤K/(rho*A^2) := (le_div_iff₀ hden).mpr (by nlinarith)
    have he : ((K/(rho*A^2))^((1 : ℝ)/3))^3 = K/(rho*A^2) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0≤K/(rho*A^2))]
      norm_num
    have hwr : w≤(K/(rho*A^2))^((1 : ℝ)/3) := by
      apply (pow_le_pow_iff_left₀ hw hroot0 (by norm_num : (3 : ℕ)≠0)).mp
      rw [he]
      exact hp
    exact (hmw.trans hwr).trans (le_add_of_nonneg_right (le_min hcap (by positivity)))
  · rw [min_eq_right (le_of_not_ge hcase)] at hcurvature
    have hp : w≤K/(h*A^2) := (le_div_iff₀ (by positivity : 0<h*A^2)).mpr (by nlinarith)
    exact (le_min hmcap (hmw.trans hp)).trans (le_add_of_nonneg_left hroot0)

theorem localization_interior_integral_bound_of_curvature (psi : ℝ→ℝ)
    (hpsi : Measurable psi) (q L beta : ℝ) (hq : q∈Ioo (0 : ℝ) 1)
    (hL : 0<L) (hbeta : 0<beta) (hbound : ∀x∈Icc (0 : ℝ) 1, |psi x|≤beta)
    (j : Fin 4) (K rho h : ℝ) (hK : 0≤K) (hrho : 0<rho) (hh : 0<h)
    (hcurvature : ∀A : ℝ, 0<A → A^2*localizationLevelMass psi q L A j*min (rho*A^2) h ≤ K) :
    (∫ A : ℝ in Ioi 0, localizationLevelMass psi q L A j) ≤
      (4/3 : ℝ)*(K/rho)^((1 : ℝ)/4) + 2*Real.sqrt (K/h) := by
  obtain ⟨hi₄,he₄⟩ := FourPapersCommon.integral_truncated_inverse_fourth (K/rho) (by positivity)
  obtain ⟨hi₂,he₂⟩ := FourPapersCommon.integral_truncated_inverse_square (K/h) (by positivity)
  have hi := integrable_localizationLevelMass psi hpsi q L beta hq hL hbeta hbound j
  have hm := setIntegral_mono_on hi (hi₄.add hi₂) measurableSet_Ioi (fun A hA => by
    have hb := interior_level_bound _ K rho h A
      (localizationLevelMass_nonneg_le_one psi q L A hq hL hA j).1
      (localizationLevelMass_nonneg_le_one psi q L A hq hL hA j).2 hK hrho hh hA (hcurvature A hA)
    rw [Real.rpow_neg hA.le, Real.rpow_neg hA.le,
      show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_two] at hb
    simpa only [Pi.add_apply,div_eq_mul_inv] using hb)
  change (∫ A : ℝ in Ioi 0, localizationLevelMass psi q L A j) ≤
    (∫ A : ℝ in Ioi 0, min 1 (K/rho/A^4)+min 1 (K/h/A^2)) at hm
  rw [integral_add hi₄ hi₂,he₄,he₂] at hm
  exact hm


theorem cubic_level_root_factor (K rho A : ℝ) (hK : 0≤K) (hrho : 0<rho) (hA : 0<A) :
    (K/(rho*A^2))^((1 : ℝ)/3) = (K/rho)^((1 : ℝ)/3)*A^(-(2/3 : ℝ)) := by
  rw [show K/(rho*A^2) = (K/rho)/(A^2) by field_simp]
  rw [Real.div_rpow (by positivity) (sq_nonneg _),
    ←Real.rpow_natCast A 2,←Real.rpow_mul hA.le]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_neg hA.le,div_eq_mul_inv]

theorem integral_cropped_inverse_two_thirds (K rho beta : ℝ)
    (_hK : 0≤K) (_hrho : 0<rho) (hbeta : 0<beta) :
    IntegrableOn ((Ioc (0 : ℝ) beta).indicator
      (fun A => (K/rho)^((1 : ℝ)/3)*A^(-(2/3 : ℝ)))) (Ioi 0) volume ∧
      (∫ A : ℝ in Ioi 0, (Ioc (0 : ℝ) beta).indicator
        (fun A => (K/rho)^((1 : ℝ)/3)*A^(-(2/3 : ℝ))) A) =
          3*beta^((1 : ℝ)/3)*(K/rho)^((1 : ℝ)/3) := by
  obtain ⟨hi,he⟩ := FourPapersCommon.integral_inverse_two_thirds beta hbeta.le
  have hiroot : IntegrableOn (fun A => (K/rho)^((1 : ℝ)/3)*A^(-(2/3 : ℝ))) (Ioc 0 beta) volume :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).mpr (hi.const_mul _)
  refine ⟨(hiroot.integrable_indicator measurableSet_Ioc).mono_measure Measure.restrict_le_self,?_⟩
  rw [integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc (0 : ℝ) beta ⊆ Ioi 0 from fun _ hx => hx.1),
    integral_Ioc_eq_integral_Ioo,MeasureTheory.integral_const_mul,he]
  ring

/-- Common boundary integration, with the geometric width and its cutoff
curvature estimate kept explicit. This covers the two actual boundary
families without assuming an already integrated level-set bound. -/
theorem localization_boundary_integral_bound_of_width_curvature (psi : ℝ→ℝ)
    (hpsi : Measurable psi) (q L beta : ℝ) (hq : q∈Ioo (0 : ℝ) 1)
    (hL : 0<L) (hbeta : 0<beta) (hbound : ∀x∈Icc (0 : ℝ) 1, |psi x|≤beta)
    (j : Fin 4) (K rho h : ℝ) (hK : 0≤K) (hrho : 0<rho) (hh : 0<h)
    (cap : ℝ→ℝ) (hcap : ∀A : ℝ, 0<A → 0≤cap A)
    (hmin : IntegrableOn (fun A => min (cap A) (K/h/A^2)) (Ioi 0) volume)
    (hwidth : ∀A : ℝ, 0<A → ∃w : ℝ, 0≤w ∧ localizationLevelMass psi q L A j≤w ∧
      w≤cap A ∧ A^2*w*min (rho*w^2) h≤K) :
    (∫ A : ℝ in Ioi 0, localizationLevelMass psi q L A j) ≤
      3*beta^((1 : ℝ)/3)*(K/rho)^((1 : ℝ)/3) +
        ∫ A : ℝ in Ioi 0, min (cap A) (K/h/A^2) := by
  have him := integrable_localizationLevelMass psi hpsi q L beta hq hL hbeta hbound j
  obtain ⟨hig,heg⟩ := integral_cropped_inverse_two_thirds K rho beta hK hrho hbeta
  have hp (A : ℝ) (hA : 0<A) : localizationLevelMass psi q L A j ≤
      (Ioc (0 : ℝ) beta).indicator (fun A => (K/rho)^((1 : ℝ)/3)*A^(-(2/3 : ℝ))) A +
        min (cap A) (K/h/A^2) := by
    by_cases hAb : A≤beta
    · rw [indicator_of_mem (show A∈Ioc (0 : ℝ) beta from ⟨hA,hAb⟩)]
      obtain ⟨w,hw,hmw,hwcap,hcurv⟩ := hwidth A hA
      have hh := boundary_level_bound _ w (cap A) K rho h A
        (localizationLevelMass_nonneg_le_one psi q L A hq hL hA j).1 hw (hcap A hA)
        hmw (hmw.trans hwcap) hK hrho hh hA hcurv
      rw [cubic_level_root_factor K rho A hK hrho hA] at hh
      convert hh using 1
      rw [div_mul_eq_div_div]
    · rw [localizationLevelMass_zero_above psi q L beta A hq hL hbeta
        (le_of_not_ge hAb) hbound j]
      exact add_nonneg (Set.indicator_nonneg (fun x hx =>
        mul_nonneg (Real.rpow_nonneg (div_nonneg hK hrho.le) _)
          (Real.rpow_nonneg hx.1.le _)) _)
        (le_min (hcap A hA) (by positivity))
  have hm := setIntegral_mono_on him (hig.add hmin) measurableSet_Ioi (fun A hA => by
    simpa only [Pi.add_apply] using hp A hA)
  change (∫ A : ℝ in Ioi 0, localizationLevelMass psi q L A j) ≤
      (∫ A : ℝ in Ioi 0,
        (Ioc (0 : ℝ) beta).indicator (fun A => (K/rho)^((1 : ℝ)/3)*A^(-(2/3 : ℝ))) A +
          min (cap A) (K/h/A^2)) at hm
  rw [integral_add hig hmin,heg] at hm
  exact hm

theorem localization_negative_boundary_integral_bound_of_width_curvature (psi : ℝ→ℝ)
    (hpsi : Measurable psi) (q L beta : ℝ) (hq : q∈Ioo (0 : ℝ) 1)
    (hL : 0<L) (hbeta : 0<beta) (hbound : ∀x∈Icc (0 : ℝ) 1, |psi x|≤beta)
    (K rho h : ℝ) (hK : 0≤K) (hrho : 0<rho) (hh : 0<h)
    (hwidth : ∀A : ℝ, 0<A → ∃w : ℝ, 0≤w ∧ localizationLevelMass psi q L A 2≤w ∧
      w≤A/(2*L) ∧ A^2*w*min (rho*w^2) h≤K) :
    (∫ A : ℝ in Ioi 0, localizationLevelMass psi q L A 2) ≤
      3*beta^((1 : ℝ)/3)*(K/rho)^((1 : ℝ)/3) +
        3*(K/h)^((2/3 : ℝ))/(2*(2*L)^((1 : ℝ)/3)) := by
  obtain ⟨hi,he⟩ := FourPapersCommon.integral_min_linear_inverse_square L (K/h) hL (by positivity)
  have hh := localization_boundary_integral_bound_of_width_curvature psi hpsi q L beta
    hq hL hbeta hbound 2 K rho h hK hrho hh (fun A => A/(2*L))
      (fun A hA => by positivity) hi hwidth
  rw [he] at hh
  exact hh

theorem localization_post_boundary_integral_bound_of_width_curvature (psi : ℝ→ℝ)
    (hpsi : Measurable psi) (q L beta : ℝ) (hq : q∈Ioo (0 : ℝ) 1)
    (hL : 0<L) (hbeta : 0<beta) (hbound : ∀x∈Icc (0 : ℝ) 1, |psi x|≤beta)
    (K rho h : ℝ) (hK : 0≤K) (hrho : 0<rho) (hh : 0<h)
    (hwidth : ∀A : ℝ, 0<A → ∃w : ℝ, 0≤w ∧ localizationLevelMass psi q L A 3≤w ∧
      w≤1 ∧ A^2*w*min (rho*w^2) h≤K) :
    (∫ A : ℝ in Ioi 0, localizationLevelMass psi q L A 3) ≤
      3*beta^((1 : ℝ)/3)*(K/rho)^((1 : ℝ)/3) + 2*Real.sqrt (K/h) := by
  obtain ⟨hi,he⟩ := FourPapersCommon.integral_truncated_inverse_square (K/h) (by positivity)
  have hh := localization_boundary_integral_bound_of_width_curvature psi hpsi q L beta
    hq hL hbeta hbound 3 K rho h hK hrho hh (fun _ => 1)
      (fun _ _ => zero_le_one) hi hwidth
  rw [he] at hh
  exact hh

end QuantitativeFollowup
