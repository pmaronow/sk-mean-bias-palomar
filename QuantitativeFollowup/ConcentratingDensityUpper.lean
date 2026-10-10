module
public import QuantitativeFollowup.ConcentratingPushedMix
public import QuantitativeFollowup.SignedDensityDomination

@[expose] public section

/-! Ordinary density domination of the actual concentrating move.
It follows from the proved signed-density identity and the genuine bound
on the increment's actual derivative. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem concentratingParisiMeasure_density_upper (μ : Paper.ParisiMeasure)
    (a ell kappa tau C : ℝ) (ha : 0 < a) (he : a+ell < 1)
    (hell : 0 < ell) (hkappa : 0 ≤ kappa) (hC : 0 ≤ C)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)))
    (hupper : (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal C • volume.restrict (Ioo a (a+ell))) :
    (parisiCDFPrimitive (concentratingParisiMeasure μ a ell kappa tau ha he hell hkappa htau hdensity)).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal (C+tau*(32/ell^2)) • volume.restrict (Ioo a (a+ell)) := by
  rw [parisiCDFPrimitive_measure] at hupper ⊢
  apply restrict_le_of_signed_density _ _ (Ioo a (a+ell)) measurableSet_Ioo
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (deriv (concentratingIntervalIncrement a ell))
    (concentratingIntervalIncrement_derivative_integrable a ell hell) tau C (32/ell^2)
    htau.1 hC (by positivity) _
    (concentratingParisiMeasure_signed_density μ a ell kappa tau ha he hell hkappa htau hdensity) hupper
  intro x _
  exact (abs_le.mp (concentratingIntervalIncrement_second_derivative_bound a ell x hell)).1

theorem concentrating_normalized_density_upper (μ : Paper.ParisiMeasure)
    (beta a ell C : ℝ) (hbeta : 0 < beta)
    (hupper : ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal C • volume.restrict (Ioo a (a+ell))) :
    (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal (C/beta) • volume.restrict (Ioo a (a+ell)) := by
  have hb : 0 ≤ 1/beta := by positivity
  calc
    _ = ENNReal.ofReal (1/beta) •
        (ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) := by
      rw [smul_smul,←ENNReal.ofReal_mul hb,one_div_mul_cancel hbeta.ne',ENNReal.ofReal_one,one_smul]
    _ ≤ ENNReal.ofReal (1/beta) • (ENNReal.ofReal C • volume.restrict (Ioo a (a+ell))) := by
      intro S
      exact mul_le_mul_of_nonneg_left (hupper S) (by positivity)
    _ = _ := by
      rw [smul_smul,←ENNReal.ofReal_mul hb]
      congr 2
      ring

theorem concentratingEnergyMeasure_density_upper (μ : Paper.ParisiMeasure)
    (beta a ell kappa tau C : ℝ) (hbeta : 0 < beta) (ha : 0 < a)
    (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa) (hC : 0 ≤ C)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)))
    (hupper : ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal C • volume.restrict (Ioo a (a+ell))) :
    ENNReal.ofReal beta • (parisiCDFPrimitive (concentratingEnergyMeasure μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity)).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal (C+tau*(32/ell^2)) • volume.restrict (Ioo a (a+ell)) := by
  have hu := concentratingParisiMeasure_density_upper μ a ell (kappa/beta) (tau/beta) (C/beta)
    ha he hell (div_nonneg hkappa hbeta.le) (div_nonneg hC hbeta.le)
    (concentrating_normalized_parameter beta ell kappa tau hbeta htau)
    (concentrating_normalized_density μ beta a ell kappa hbeta hkappa hdensity)
    (concentrating_normalized_density_upper μ beta a ell C hbeta hupper)
  calc
    _ ≤ ENNReal.ofReal beta • (ENNReal.ofReal (C/beta+(tau/beta)*(32/ell^2)) • volume.restrict (Ioo a (a+ell))) := by
      intro S
      exact mul_le_mul_of_nonneg_left (hu S) (by positivity)
    _ = _ := by
      rw [smul_smul,←ENNReal.ofReal_mul hbeta.le]
      congr 2
      field_simp

end QuantitativeFollowup
