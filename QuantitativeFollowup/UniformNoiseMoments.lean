module
public import QuantitativeFollowup.ReflectedNoise
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Exact moments of the genuine uniform perturbation. These establish
the numerical `h²/6` averaging constant in reflected regularization. -/
noncomputable section
open Set MeasureTheory Paper
open scoped ENNReal
namespace QuantitativeFollowup

theorem integrable_symmetricUniformLaw_id (h : ℝ) : Integrable (fun u : ℝ=>u) (symmetricUniformLaw h) := by
  have hi : Integrable (fun u : ℝ=>u) (volume.restrict (Icc (-h) h)):=continuous_id.continuousOn.integrableOn_compact isCompact_Icc
  exact hi.smul_measure ENNReal.ofReal_ne_top

theorem integrable_symmetricUniformLaw_sq (h : ℝ) : Integrable (fun u : ℝ=>u^2) (symmetricUniformLaw h) := by
  have hi : Integrable (fun u : ℝ=>u^2) (volume.restrict (Icc (-h) h)):=(continuous_id.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hi.smul_measure ENNReal.ofReal_ne_top

theorem symmetricUniformLaw_mean (h : ℝ) (hh : 0<h) :
    (∫u,u∂symmetricUniformLaw h)=0 := by
  rw [symmetricUniformLaw,integral_smul_measure,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by linarith : -h≤h),integral_id]
  simp

theorem symmetricUniformLaw_secondMoment (h : ℝ) (hh : 0<h) :
    (∫u,u^2∂symmetricUniformLaw h)=h^2/3 := by
  rw [symmetricUniformLaw,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),
    integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by linarith : -h≤h),integral_pow]
  simp only [smul_eq_mul]
  field_simp
  ring

theorem reflected_uniform_taylor_average_le (h : ℝ) (hh : h∈Ioc (0:ℝ) (1/2))
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) (G : ℝ→ℝ) (hG : Continuous G) (a : ℝ)
    (htaylor : ∀u∈Icc (-h) h,G (overlapReflection (q+u))≤G q+a*u+u^2/2) :
    (∫u,G (overlapReflection (q+u))∂symmetricUniformLaw h)-G q≤h^2/6 := by
  have:=symmetricUniformLaw_probability h hh.1
  obtain ⟨K,hK⟩:=isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  have hi : Integrable (fun u=>G (overlapReflection (q+u))) (symmetricUniformLaw h) := by
    apply (integrable_const K).mono' (hG.measurable.comp
      (measurable_overlapReflection.comp (measurable_const.add measurable_id))).aestronglyMeasurable
    filter_upwards [symmetricUniformLaw_ae h] with u hu
    exact hK _ (overlapReflection_mem hq hh hu)
  have hia : Integrable (fun u : ℝ=>G q+a*u+u^2/2) (symmetricUniformLaw h) :=
    ((integrable_const _).add ((integrable_symmetricUniformLaw_id h).const_mul a)).add
      ((integrable_symmetricUniformLaw_sq h).div_const 2)
  have hiq:=integral_mono_ae hi hia (by
    filter_upwards [symmetricUniformLaw_ae h] with u hu
    exact htaylor u hu)
  rw [integral_add (f:=fun u : ℝ=>G q+a*u) (g:=fun u : ℝ=>u^2/2) ((integrable_const _).add ((integrable_symmetricUniformLaw_id h).const_mul a))
    ((integrable_symmetricUniformLaw_sq h).div_const 2),
    integral_add (f:=fun _u : ℝ=>G q) (g:=fun u : ℝ=>a*u) (integrable_const _) ((integrable_symmetricUniformLaw_id h).const_mul a),
    integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul,
    integral_const_mul,integral_div,symmetricUniformLaw_mean h hh.1,
    symmetricUniformLaw_secondMoment h hh.1,mul_zero,add_zero] at hiq
  linarith

end QuantitativeFollowup
