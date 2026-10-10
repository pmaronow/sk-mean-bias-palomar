module
public import QuantitativeFollowup.ConcentratingMixedDensity
public import QuantitativeFollowup.FreeMeasureContact

@[expose] public section

/-! The actual pushed probability mixing segment used in root localization.
All profiles are constructed measures, including at the zero parameter. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem concentrating_half_room_parameter (ell kappa tau : ℝ) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/64)) :
    tau ∈ Icc (0 : ℝ) (kappa*ell^2/32) := by
  refine ⟨htau.1,?_⟩
  nlinarith [htau.2,mul_nonneg hkappa (sq_nonneg ell)]

def concentratingPushedMix (μ ν : Paper.ParisiMeasure)
    (beta a ell kappa tau theta : ℝ) (hbeta : 0 < beta)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/64))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell))) : Paper.ParisiMeasure :=
  parisiMix μ (concentratingEnergyMeasure ν beta a ell kappa tau hbeta ha he hell hkappa
    (concentrating_half_room_parameter ell kappa tau hkappa htau) hdensity) theta

theorem concentratingPushedMix_profile (μ ν : Paper.ParisiMeasure)
    (beta a ell kappa tau theta : ℝ) (hbeta : 0 < beta)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/64)) (htheta : theta ∈ Icc (0 : ℝ) 1)
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell))) (x : ℝ) :
    beta*parisiCDF (concentratingPushedMix μ ν beta a ell kappa tau theta hbeta ha he hell hkappa htau hdensity) x=
      beta*parisiCDF (parisiMix μ ν theta) x-(theta*tau)*concentratingIntervalIncrement a ell x := by
  rw [concentratingPushedMix,parisiCDF_mix _ _ theta x htheta,parisiCDF_mix μ ν theta x htheta]
  have hp := concentratingEnergyMeasure_profile ν beta a ell kappa tau hbeta ha he hell hkappa
    (concentrating_half_room_parameter ell kappa tau hkappa htau) hdensity x
  have hh := congrArg (fun z : ℝ => theta*z) hp
  nlinarith

theorem concentratingPushedMix_mem_floor (μ ν : Paper.ParisiMeasure)
    (beta a ell kappa tau theta s : ℝ) (hbeta : 0 < beta)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/64)) (htheta : theta ∈ Icc (0 : ℝ) 1)
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell)))
    (hμ : μ ∈ scalarFloor s) (hν : ν ∈ scalarFloor s) :
    concentratingPushedMix μ ν beta a ell kappa tau theta hbeta ha he hell hkappa htau hdensity ∈ scalarFloor s :=
  parisiMix_mem_scalarFloor hμ
    (concentratingEnergyMeasure_preserves_floor ν beta a ell kappa tau s hbeta ha he hell hkappa
      (concentrating_half_room_parameter ell kappa tau hkappa htau) hdensity hν) htheta

theorem concentratingPushedMix_eq_mixed_move (μ ν : Paper.ParisiMeasure)
    (beta a ell kappa tau theta : ℝ) (hbeta : 0 < beta)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/64)) (htheta : theta ∈ Icc (0 : ℝ) 1)
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell))) :
    concentratingPushedMix μ ν beta a ell kappa tau theta hbeta ha he hell hkappa htau hdensity=
      concentratingEnergyMeasure (parisiMix μ ν theta) beta a ell (theta*kappa) (theta*tau)
        hbeta ha he hell (mul_nonneg htheta.1 hkappa)
        (concentrating_mixed_parameter ell kappa tau theta hkappa htau htheta).1
        (concentrating_mixed_density μ ν beta a ell kappa theta htheta hdensity) := by
  apply FRSB.eq_of_parisiCDF_ae_eq
  apply Filter.Eventually.of_forall
  intro x
  have h1 := concentratingPushedMix_profile μ ν beta a ell kappa tau theta hbeta ha he hell hkappa htau htheta hdensity x
  have h2 := concentratingEnergyMeasure_profile (parisiMix μ ν theta) beta a ell (theta*kappa) (theta*tau)
    hbeta ha he hell (mul_nonneg htheta.1 hkappa)
    (concentrating_mixed_parameter ell kappa tau theta hkappa htau htheta).1
    (concentrating_mixed_density μ ν beta a ell kappa theta htheta hdensity) x
  nlinarith

end QuantitativeFollowup
