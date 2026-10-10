module
public import QuantitativeFollowup.ConcentratingMeasure
public import Paper.JTVariational

@[expose] public section

/-! Literal affine segments of the constructed probability measures.
Both normalization and the zero-atom constraint have already been proved. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB
open scoped Topology ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem parisiCDF_one_of_one_le (μ : Paper.ParisiMeasure) (x : ℝ) (hx : 1 ≤ x) :
    parisiCDF μ x = 1 := by
  unfold parisiCDF
  have hs : {q : Paper.Overlap | (q : ℝ) ≤ x} = univ :=
    Set.eq_univ_of_forall (fun q => q.property.2.trans hx)
  rw [hs, measure_univ, ENNReal.toReal_one]

theorem concentratingParisiMeasure_cdf_all (μ : Paper.ParisiMeasure)
    (a ell kappa tau : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) (x : ℝ) :
    parisiCDF (concentratingParisiMeasure μ a ell kappa tau ha he hell hkappa htau hdensity) x =
      parisiCDF μ x - tau*concentratingIntervalIncrement a ell x := by
  by_cases hx0 : x < 0
  · rw [parisiCDF_eq_zero_of_lt_zero _ hx0, parisiCDF_eq_zero_of_lt_zero μ hx0,
      concentratingIntervalIncrement_zero_outside a ell x hell (fun h => by linarith [h.1]),
      mul_zero, sub_zero]
  · by_cases hx1 : 1 ≤ x
    · rw [parisiCDF_one_of_one_le _ x hx1, parisiCDF_one_of_one_le μ x hx1,
        concentratingIntervalIncrement_zero_outside a ell x hell (fun h => by linarith [h.2]),
        mul_zero, sub_zero]
    · exact concentratingParisiMeasure_cdf μ a ell kappa tau ha he hell hkappa htau hdensity x
        ⟨le_of_not_gt hx0, (lt_of_not_ge hx1).le⟩

theorem concentratingParisiMeasure_primitive (μ : Paper.ParisiMeasure)
    (a ell kappa tau : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) :
    parisiCDFPrimitive (concentratingParisiMeasure μ a ell kappa tau ha he hell hkappa htau hdensity) =
      concentratingMovedStieltjes (parisiCDFPrimitive μ) a ell kappa tau hell hkappa htau hdensity := by
  ext x
  exact concentratingParisiMeasure_cdf_all μ a ell kappa tau ha he hell hkappa htau hdensity x

theorem concentratingParisiMeasure_affine (μ : Paper.ParisiMeasure)
    (a ell kappa tau theta : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32)) (htheta : theta ∈ Icc (0 : ℝ) 1)
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)))
    (hproduct : theta*tau ∈ Icc (0 : ℝ) (kappa*ell^2/32)) :
    concentratingParisiMeasure μ a ell kappa (theta*tau) ha he hell hkappa hproduct hdensity =
      parisiMix μ (concentratingParisiMeasure μ a ell kappa tau ha he hell hkappa htau hdensity) theta := by
  apply eq_of_parisiCDF_ae_eq
  apply Filter.Eventually.of_forall
  intro x
  rw [concentratingParisiMeasure_cdf_all μ a ell kappa (theta*tau) ha he hell hkappa hproduct hdensity,
    parisiCDF_mix _ _ theta x htheta,
    concentratingParisiMeasure_cdf_all μ a ell kappa tau ha he hell hkappa htau hdensity]
  ring

theorem concentrating_parameter_product_mem (ell kappa tau theta : ℝ)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32)) (htheta : theta ∈ Icc (0 : ℝ) 1) :
    theta*tau ∈ Icc (0 : ℝ) (kappa*ell^2/32) :=
  ⟨mul_nonneg htheta.1 htau.1,
    (mul_le_mul_of_nonneg_right htheta.2 htau.1).trans (by simpa only [one_mul] using htau.2)⟩

end QuantitativeFollowup
