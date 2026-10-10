module
public import FourPapersCommon.L2IntegralBounds
public import Mathlib.Probability.Moments.Basic

@[expose] public section

/-! A genuine Paley--Zygmund estimate for the exponential tilt used in the
sixth-power window. The event estimate follows from integral Cauchy--Schwarz. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
set_option maxHeartbeats 1000000

theorem paley_zygmund_half_square (Z : Ω → ℝ) (hZm : Measurable Z)
    (hZ : MemLp Z 2 P) (hZnon : ∀ ω, 0 ≤ Z ω) :
    (∫ ω, Z ω ∂P)^2/4 ≤
      P.real {ω | (∫ η, Z η ∂P)/2 ≤ Z ω} * (∫ ω, Z ω^2 ∂P) := by
  let m := ∫ ω, Z ω ∂P
  let A : Set Ω := {ω | m/2 ≤ Z ω}
  have hA : MeasurableSet A := measurableSet_le measurable_const hZm
  have hi : Integrable Z P := hZ.integrable (by norm_num)
  have hi2 : Integrable (fun ω => Z ω^2) P := hZ.integrable_sq
  have hm : 0 ≤ m := integral_nonneg hZnon
  have hsmall : ∫ ω in Aᶜ, Z ω ∂P ≤ m/2 := by
    have hh := setIntegral_mono_on (hi.restrict (s:=Aᶜ))
      (integrable_const (m/2) : Integrable (fun _ : Ω => m/2) (P.restrict Aᶜ))
      hA.compl (fun ω hω => le_of_lt (lt_of_not_ge hω))
    have hp : P.real Aᶜ ≤ 1 := measureReal_le_one
    simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ] at hh
    nlinarith
  have hsplit : (∫ ω in A, Z ω ∂P)+(∫ ω in Aᶜ, Z ω ∂P)=m :=
    integral_add_compl hA hi
  have hbig : m/2 ≤ ∫ ω in A, Z ω ∂P := by linarith
  have hbigNon : 0 ≤ ∫ ω in A, Z ω ∂P := integral_nonneg hZnon
  have hcs := FourPapersCommon.integral_sq_le_mass_mul_integral_sq Z (hZ.restrict A)
  have hsq : ∫ ω in A, Z ω^2 ∂P ≤ ∫ ω, Z ω^2 ∂P :=
    setIntegral_le_integral hi2 (Filter.Eventually.of_forall fun ω => sq_nonneg (Z ω))
  have hpNon : 0 ≤ P.real A := measureReal_nonneg
  simp only [measureReal_restrict_apply_univ] at hcs
  have hh : (∫ ω in A, Z ω ∂P)^2 ≤ P.real A*(∫ ω, Z ω^2 ∂P) := by
    exact hcs.trans (mul_le_mul_of_nonneg_left hsq hpNon)
  change m^2/4 ≤ P.real A*(∫ ω, Z ω^2 ∂P)
  nlinarith

theorem paley_zygmund_half (Z : Ω → ℝ) (hZm : Measurable Z)
    (hZ : MemLp Z 2 P) (hZnon : ∀ ω, 0 ≤ Z ω)
    (hZ2 : 0 < ∫ ω, Z ω^2 ∂P) :
    (∫ ω, Z ω ∂P)^2/(4*(∫ ω, Z ω^2 ∂P)) ≤
      P.real {ω | (∫ η, Z η ∂P)/2 ≤ Z ω} := by
  have hh := paley_zygmund_half_square Z hZm hZ hZnon
  apply (div_le_iff₀ (by positivity : 0<4*(∫ ω, Z ω^2 ∂P))).2
  nlinarith

end QuantitativePaper
