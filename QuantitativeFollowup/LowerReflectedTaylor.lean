module
public import QuantitativeFollowup.TransportDeficitTaylor
public import QuantitativeFollowup.LowerReflectedDensity

@[expose] public section

/-! Exact noise Taylor averaging for the lower-only fold on the larger
radius interval `0<h≤1−T`. This is the geometry of partial regularization. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 800000

theorem uniform_noise_taylor_average_le (h : ℝ) (hh : 0<h) (q : ℝ)
    (G : ℝ→ℝ) (hG : Continuous G) (Φ : ℝ→ℝ) (hΦ : Measurable Φ) (a : ℝ)
    (hrange : ∀ᵐu∂symmetricUniformLaw h,Φ u∈Icc (0:ℝ) 1)
    (htaylor : ∀ᵐu∂symmetricUniformLaw h,G (Φ u)≤G q+a*u+u^2/2) :
    (∫u,G (Φ u)∂symmetricUniformLaw h)-G q≤h^2/6 := by
  letI:=symmetricUniformLaw_probability h hh
  obtain ⟨K,hK⟩:=isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  have hi : Integrable (fun u=>G (Φ u)) (symmetricUniformLaw h):=
    (integrable_const K).mono' (hG.measurable.comp hΦ).aestronglyMeasurable
      (hrange.mono fun u hu=>hK _ hu)
  have hia : Integrable (fun u : ℝ=>G q+a*u+u^2/2) (symmetricUniformLaw h):=
    ((integrable_const _).add ((integrable_symmetricUniformLaw_id h).const_mul a)).add
      ((integrable_symmetricUniformLaw_sq h).div_const 2)
  have hm:=integral_mono_ae hi hia htaylor
  rw [integral_add (f:=fun u : ℝ=>G q+a*u) (g:=fun u : ℝ=>u^2/2)
      ((integrable_const _).add ((integrable_symmetricUniformLaw_id h).const_mul a))
      ((integrable_symmetricUniformLaw_sq h).div_const 2),
    integral_add (f:=fun _u : ℝ=>G q) (g:=fun u : ℝ=>a*u) (integrable_const _)
      ((integrable_symmetricUniformLaw_id h).const_mul a),
    integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul,
    integral_const_mul,integral_div,symmetricUniformLaw_mean h hh,
    symmetricUniformLaw_secondMoment h hh,mul_zero,add_zero] at hm
  linarith

theorem transportDeficit_lower_reflected_uniform_bound (S : ℝ→ℝ) (hS : Continuous S)
    (hmono : MonotoneOn S (Icc (0:ℝ) 1))
    (hbound : ∀q∈Icc (0:ℝ) 1,0≤S q ∧ S q≤1)
    (T h : ℝ) (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T))
    (q : ℝ) (hq : q∈Ico (0:ℝ) T) :
    (∫u,transportDeficit S |q+u|∂symmetricUniformLaw h)-transportDeficit S q≤h^2/6 := by
  have hq1:q∈Icc (0:ℝ) 1:=⟨hq.1,hq.2.le.trans hT.2.le⟩
  have hy : ∀ᵐu∂symmetricUniformLaw h,|q+u|∈Icc (0:ℝ) 1 := by
    filter_upwards [symmetricUniformLaw_ae h] with u hu
    refine ⟨abs_nonneg _,?_⟩
    rw [abs_le]
    constructor <;>linarith [hq.1,hq.2,hT.1,hh.2,hu.1,hu.2]
  apply uniform_noise_taylor_average_le h hh.1 q (transportDeficit S) (continuous_transportDeficit S hS)
    (fun u=>|q+u|) (measurable_const.add measurable_id).abs (q-S q) hy
  filter_upwards [symmetricUniformLaw_ae h,hy] with u hu hyr
  have hz:q+u≤1:=by linarith [hq.2,hh.2,hu.2]
  have hπ:overlapReflection (q+u)=|q+u|:=by simp only [overlapReflection,ite_eq_left hz]
  rw [←hπ] at hyr ⊢
  exact transportDeficit_reflected_taylor S hS hmono hbound q u hq1 hyr

end QuantitativeFollowup
