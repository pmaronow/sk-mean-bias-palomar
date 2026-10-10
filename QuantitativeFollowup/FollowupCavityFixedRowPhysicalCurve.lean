module
public import QuantitativeFollowup.FollowupCavityFixedRowTwoClockCovariance
public import QuantitativeFollowup.FollowupCavityMixtureMovingCovariance

@[expose] public section

/-! Exact identification of the original physical u-curve with the
Z-weighted two-clock covariance, including the moving last-field variance. -/
noncomputable section
open Set QuantitativePaper FourPapersCommon SpinGlass.Targets
namespace QuantitativeFollowup
variable {n k : ℕ}
set_option maxHeartbeats 1700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem cavityFixedRowPhysicalCurveCovariance_eq_moving
    (hn : 0<n) (beta rho : ℝ) (hbeta : 0<beta) (hrho : rho∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    cavityFixedRowPhysicalCurveCovariance (n:=n) beta rho hbeta hrho s a d u=
      cavityMovingRowWeightedCovariance (n := n)
        (cavityFixedRowMovingNormalizer beta rho hbeta hrho s a)
        (cavityFixedRowMovingLastMean beta rho hbeta hrho s a d)
        (cavityFixedRowMovingRestMean beta rho hbeta hrho s a d)
        (cavityFixedRowMovingProductMean beta rho hbeta hrho s a d)
        (followupCavityD n beta rho) (n:ℝ) (followupCavityAlpha n beta rho/(n:ℝ)*u) := by
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hb : 0<followupCavityB n beta rho u :=
    (mul_pos (sq_pos_of_pos hbeta) hrho.1).trans_le (followupCavityB_window n beta rho u hrho.2 hu).1
  have hv : 0≤followupCavityAlpha n beta rho*u/(n:ℝ) :=
    div_nonneg (mul_nonneg (followupCavityAlpha_nonneg n beta rho hrho.2) hu.1) (Nat.cast_nonneg n)
  have hrow : followupCavityAlpha n beta rho*u/(n:ℝ)=followupCavityAlpha n beta rho/(n:ℝ)*u := by ring
  have hclock : followupCavityD n beta rho-(n:ℝ)*(followupCavityAlpha n beta rho/(n:ℝ)*u)=
      followupCavityB n beta rho u := by
    unfold followupCavityB
    field_simp [hn']
    <;> ring
  rw [cavityFixedRowPhysicalCurveCovariance_eq beta rho hbeta hrho s a d u hu,
    ←cavityFixedRowTwoClockModel_physical beta rho hbeta hrho u hu hb,
    cavityFixedRowTwoClockCovariance_eq_weighted beta rho hbeta hrho s a d
      (followupCavityB n beta rho u) hb (followupCavityAlpha n beta rho*u/(n:ℝ)) hv,hrow]
  simp only [cavityMovingRowWeightedCovariance,cavityFixedRowMovingNormalizer,
    cavityFixedRowMovingLastMean,cavityFixedRowMovingRestMean,cavityFixedRowMovingProductMean,hclock,
    cavityFixedRowPositiveVarianceModel_eq beta rho hbeta hrho _ hb]

end QuantitativeFollowup
