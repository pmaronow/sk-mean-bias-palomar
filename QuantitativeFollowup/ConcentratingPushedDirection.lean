module
public import QuantitativeFollowup.ConcentratingPushedDensity

@[expose] public section

/-! The literal CDF direction and its sign after the actual concentrating
push. The half-room constraint controls the perturbation by kappa*ell/16. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

def concentratingPushedDirection (μ ν : Paper.ParisiMeasure)
    (beta a ell tau x : ℝ) : ℝ :=
  beta*parisiCDF ν x-beta*parisiCDF μ x-tau*concentratingIntervalIncrement a ell x

theorem concentratingPushedMix_direction (μ ν : Paper.ParisiMeasure)
    (beta a ell kappa tau theta : ℝ) (hbeta : 0 < beta)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/64)) (htheta : theta ∈ Icc (0 : ℝ) 1)
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell))) (x : ℝ) :
    beta*parisiCDF (concentratingPushedMix μ ν beta a ell kappa tau theta hbeta ha he hell hkappa htau hdensity) x=
      beta*parisiCDF μ x+theta*concentratingPushedDirection μ ν beta a ell tau x := by
  rw [concentratingPushedMix_profile μ ν beta a ell kappa tau theta hbeta ha he hell hkappa htau htheta hdensity,
    parisiCDF_mix μ ν theta x htheta,concentratingPushedDirection]
  ring

theorem concentratingPushedDirection_lower (μ ν : Paper.ParisiMeasure)
    (beta a ell kappa tau A : ℝ) (hell : 0 < ell)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/64))
    (hgap : ∀x∈Ioo a (a+ell), A ≤ beta*parisiCDF ν x-beta*parisiCDF μ x) :
    ∀x∈Ioo a (a+ell), A-kappa*ell/16 ≤ concentratingPushedDirection μ ν beta a ell tau x := by
  have hτ : tau*(4/ell) ≤ kappa*ell/16 := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hell).mpr
    nlinarith [htau.2]
  intro x hx
  have hchi := concentratingIntervalIncrement_bound a ell x hell
  have hh : tau*concentratingIntervalIncrement a ell x ≤ tau*(4/ell) :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hchi) htau.1
  unfold concentratingPushedDirection
  linarith [hgap x hx]

theorem concentratingPushedDirection_root_sign (μ ν : Paper.ParisiMeasure)
    (beta q k tau : ℝ) (hq : 0 < q)
    (htau : tau ∈ Icc (0 : ℝ) ((k/2)*(q/2)^2/64))
    (hgap : ∀x∈Ioo (q/4) (3*q/4), k*q/8 ≤ beta*parisiCDF ν x-beta*parisiCDF μ x)
    (hk : 0 ≤ k) :
    ∀x∈Ioo (q/4) (3*q/4), k*q/16 ≤ concentratingPushedDirection μ ν beta (q/4) (q/2) tau x := by
  have hb : q/4+q/2=3*q/4 := by ring
  have hh := concentratingPushedDirection_lower μ ν beta (q/4) (q/2) (k/2) tau (k*q/8)
    (half_pos hq) htau (by simpa only [hb] using hgap)
  intro x hx
  have h := hh x (by simpa only [hb] using hx)
  have hkn := mul_nonneg hk hq.le
  nlinarith

end QuantitativeFollowup
