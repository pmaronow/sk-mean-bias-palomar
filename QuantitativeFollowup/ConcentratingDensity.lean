module
public import QuantitativeFollowup.ConcentratingSegment
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.VectorMeasure.Operations

@[expose] public section

/-! Actual signed Stieltjes measure of the concentrating move. The density
is the derivative of the genuine Lipschitz increment, and has total mass zero.
The measure identity is proved on a generating pi-system and the whole space. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB
open scoped Topology ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem concentratingIntervalIncrement_absoluteContinuous (a ell x y : ℝ) (hell : 0 < ell) :
    AbsolutelyContinuousOnInterval (concentratingIntervalIncrement a ell) x y :=
  (lipschitz_concentratingIntervalIncrement a ell hell).lipschitzOnWith.absolutelyContinuousOnInterval

theorem concentratingIntervalIncrement_derivative_integral (a ell x y : ℝ) (hell : 0 < ell) :
    (∫ z in x..y, deriv (concentratingIntervalIncrement a ell) z) =
      concentratingIntervalIncrement a ell y - concentratingIntervalIncrement a ell x :=
  (concentratingIntervalIncrement_absoluteContinuous a ell x y hell).integral_deriv_eq_sub

theorem concentratingIntervalIncrement_derivative_support (a ell : ℝ) (hell : 0 < ell) :
    Function.support (deriv (concentratingIntervalIncrement a ell)) ⊆ Icc a (a+ell) := by
  have hs : Function.support (concentratingIntervalIncrement a ell) ⊆ Icc a (a+ell) := by
    intro x hx
    by_contra hn
    exact hx (concentratingIntervalIncrement_zero_outside a ell x hell
      (fun h => hn ⟨h.1.le,h.2.le⟩))
  exact support_deriv_subset.trans (closure_minimal hs isClosed_Icc)

theorem concentratingIntervalIncrement_derivative_integrable (a ell : ℝ) (hell : 0 < ell) :
    Integrable (deriv (concentratingIntervalIncrement a ell)) volume := by
  have hac := concentratingIntervalIncrement_absoluteContinuous a ell (a-1) (a+ell+1) hell
  have hs : Function.support (deriv (concentratingIntervalIncrement a ell)) ⊆ Ioc (a-1) (a+ell+1) := by
    intro x hx
    have h := concentratingIntervalIncrement_derivative_support a ell hell hx
    exact ⟨by linarith [h.1],by linarith [h.2]⟩
  exact (integrableOn_iff_integrable_of_support_subset hs).mp hac.intervalIntegrable_deriv.1

theorem concentratingIntervalIncrement_derivative_total_zero (a ell : ℝ) (hell : 0 < ell) :
    (∫ x, deriv (concentratingIntervalIncrement a ell) x) = 0 := by
  have hs : Function.support (deriv (concentratingIntervalIncrement a ell)) ⊆ Ioc (a-1) (a+ell+1) := by
    intro x hx
    have h := concentratingIntervalIncrement_derivative_support a ell hell hx
    exact ⟨by linarith [h.1],by linarith [h.2]⟩
  rw [←intervalIntegral.integral_eq_integral_of_support_subset hs,
    concentratingIntervalIncrement_derivative_integral a ell (a-1) (a+ell+1) hell,
    concentratingIntervalIncrement_zero_outside a ell (a+ell+1) hell (fun h => by linarith [h.2]),
    concentratingIntervalIncrement_zero_outside a ell (a-1) hell (fun h => by linarith [h.1]),
    sub_self]

theorem concentratingParisiMeasure_signed_density (μ : Paper.ParisiMeasure)
    (a ell kappa tau : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) :
    (((concentratingParisiMeasure μ a ell kappa tau ha he hell hkappa htau hdensity : Paper.ParisiMeasure) :
      Measure Paper.Overlap).map Subtype.val).toSignedMeasure =
      ((μ : Measure Paper.Overlap).map Subtype.val).toSignedMeasure -
        tau • volume.withDensityᵥ (deriv (concentratingIntervalIncrement a ell)) := by
  let ν := concentratingParisiMeasure μ a ell kappa tau ha he hell hkappa htau hdensity
  have hi := concentratingIntervalIncrement_derivative_integrable a ell hell
  apply VectorMeasure.ext_of_generateFrom {S : Set ℝ | ∃ l u, l < u ∧ Ioc l u = S}
  · rintro S ⟨l,u,hlu,rfl⟩
    rw [Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
      _root_.sub_apply, _root_.smul_apply,
      Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
      withDensityᵥ_apply hi measurableSet_Ioc, smul_eq_mul]
    change (((ν : Measure Paper.Overlap).map Subtype.val) (Ioc l u)).toReal =
      (((μ : Measure Paper.Overlap).map Subtype.val) (Ioc l u)).toReal -
        tau*(∫ x in Ioc l u, deriv (concentratingIntervalIncrement a ell) x)
    rw [←parisiCDFPrimitive_measure ν, ←parisiCDFPrimitive_measure μ]
    have hn : 0 ≤ parisiCDFPrimitive ν u-parisiCDFPrimitive ν l :=
      sub_nonneg.mpr ((parisiCDFPrimitive ν).mono hlu.le)
    have hm : 0 ≤ parisiCDFPrimitive μ u-parisiCDFPrimitive μ l :=
      sub_nonneg.mpr ((parisiCDFPrimitive μ).mono hlu.le)
    rw [StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
      ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal hm,
      ←intervalIntegral.integral_of_le hlu.le,
      concentratingIntervalIncrement_derivative_integral a ell l u hell]
    dsimp only [ν]
    rw [parisiCDFPrimitive_apply, parisiCDFPrimitive_apply,
      concentratingParisiMeasure_cdf_all μ a ell kappa tau ha he hell hkappa htau hdensity u,
      concentratingParisiMeasure_cdf_all μ a ell kappa tau ha he hell hkappa htau hdensity l]
    simp only [parisiCDFPrimitive_apply]
    ring
  · exact BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc ℝ)
  · exact isPiSystem_Ioc (id : ℝ → ℝ) (id : ℝ → ℝ)
  · rw [Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
      _root_.sub_apply, _root_.smul_apply,
      Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
      withDensityᵥ_apply hi MeasurableSet.univ]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, setIntegral_univ,
      concentratingIntervalIncrement_derivative_total_zero a ell hell, smul_zero, sub_zero]

end QuantitativeFollowup
