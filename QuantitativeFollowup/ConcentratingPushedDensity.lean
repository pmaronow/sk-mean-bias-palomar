module
public import QuantitativeFollowup.ConcentratingDensityUpper

@[expose] public section

/-! The genuine density upper bound on the pushed segment. Its extra
curvature density is controlled by the literal half-room condition. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem concentrating_mixed_density_upper (μ ν : Paper.ParisiMeasure)
    (beta a ell C D theta : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (htheta : theta ∈ Icc (0 : ℝ) 1)
    (hμ : ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal C • volume.restrict (Ioo a (a+ell)))
    (hν : ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal D • volume.restrict (Ioo a (a+ell))) :
    ENNReal.ofReal beta • (parisiCDFPrimitive (parisiMix μ ν theta)).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal (C+D) • volume.restrict (Ioo a (a+ell)) := by
  have hθ1 := sub_nonneg.mpr htheta.2
  have hcomp : (1-theta)*C+theta*D ≤ C+D := by
    nlinarith [mul_nonneg htheta.1 hC,mul_nonneg hθ1 hD]
  calc
    _ = ENNReal.ofReal (1-theta) • (ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)))+
        ENNReal.ofReal theta • (ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell))) := by
      rw [parisiCDFPrimitive_mix_measure μ ν theta htheta,Measure.restrict_add,Measure.restrict_smul,Measure.restrict_smul,smul_add]
      ext S
      simp only [Measure.smul_apply,Measure.add_apply,smul_eq_mul]
      ring
    _ ≤ ENNReal.ofReal (1-theta) • (ENNReal.ofReal C • volume.restrict (Ioo a (a+ell)))+
        ENNReal.ofReal theta • (ENNReal.ofReal D • volume.restrict (Ioo a (a+ell))) := by
      intro S
      exact add_le_add (mul_le_mul_of_nonneg_left (hμ S) (by positivity))
        (mul_le_mul_of_nonneg_left (hν S) (by positivity))
    _ = ENNReal.ofReal ((1-theta)*C+theta*D) • volume.restrict (Ioo a (a+ell)) := by
      rw [smul_smul,smul_smul,←ENNReal.ofReal_mul hθ1,←ENNReal.ofReal_mul htheta.1,
        ←add_smul,←ENNReal.ofReal_add (mul_nonneg hθ1 hC) (mul_nonneg htheta.1 hD)]
    _ ≤ _ := by
      intro S
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcomp) (by positivity)

theorem concentratingPushedMix_density_upper (μ ν : Paper.ParisiMeasure)
    (beta a ell kappa tau theta C D : ℝ) (hbeta : 0 < beta)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/64)) (htheta : theta ∈ Icc (0 : ℝ) 1)
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell)))
    (hμ : ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal C • volume.restrict (Ioo a (a+ell)))
    (hν : ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal D • volume.restrict (Ioo a (a+ell))) :
    ENNReal.ofReal beta •
      (parisiCDFPrimitive (concentratingPushedMix μ ν beta a ell kappa tau theta hbeta ha he hell hkappa htau hdensity)).measure.restrict (Ioo a (a+ell)) ≤
        ENNReal.ofReal (C+D+kappa/2) • volume.restrict (Ioo a (a+ell)) := by
  rw [concentratingPushedMix_eq_mixed_move μ ν beta a ell kappa tau theta hbeta ha he hell hkappa htau htheta hdensity]
  have hu := concentratingEnergyMeasure_density_upper (parisiMix μ ν theta)
    beta a ell (theta*kappa) (theta*tau) (C+D) hbeta ha he hell
    (mul_nonneg htheta.1 hkappa) (add_nonneg hC hD)
    (concentrating_mixed_parameter ell kappa tau theta hkappa htau htheta).1
    (concentrating_mixed_density μ ν beta a ell kappa theta htheta hdensity)
    (concentrating_mixed_density_upper μ ν beta a ell C D theta hC hD htheta hμ hν)
  apply hu.trans
  have hτK : tau*(32/ell^2) ≤ kappa/2 := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hell)).mpr
    nlinarith [htau.2]
  have hθK : (theta*tau)*(32/ell^2) ≤ kappa/2 := by
    have hh := mul_le_mul_of_nonneg_left hτK htheta.1
    nlinarith [mul_nonneg (sub_nonneg.mpr htheta.2) hkappa]
  intro S
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (add_le_add (le_refl (C+D)) hθK)) (by positivity)

end QuantitativeFollowup
