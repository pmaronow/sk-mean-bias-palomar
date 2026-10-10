module
public import QuantitativeFollowup.FollowupCavityFixedRowPhysicalDerivativeInputs
public import QuantitativeFollowup.FollowupCavityFixedRowDerivative
public import QuantitativeFollowup.FollowupCavityMixtureFixedRowHeatData

@[expose] public section

/-! The actual physical zero-response identity. The four local heat inputs
are constructed from the normalized recorded laws. All positive last
variances have zero baseline covariance, so the original physical curve
has the same initial response as the fixed-last-variance curve. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem hasDerivWithinAt_cavityFixedRowPhysicalCurveCovariance_zero
    (hn : 0 < n) (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc (0 : ℝ) 1) (s : RSBScheme k) (a : ℝ)
    (d : ℕ) (hd : d ≤ k+2) :
    let D0 := followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl, zero_le_one⟩
    HasDerivWithinAt (cavityFixedRowPhysicalCurveCovariance (n := n) beta rho hbeta hrho s a d)
      (followupCavityAlpha n beta rho / (2*(n : ℝ)) *
        cavityRowHessianTrace (cavityFixedRowCovariance D0 s a d)) (Icc (0 : ℝ) 1) 0 := by
  obtain ⟨l,r,hl,hband,⟨hZ⟩,⟨hZf⟩,⟨hZg⟩,⟨hZh⟩⟩ :=
    exists_cavityFixedRowMovingHeatData (n := n) beta rho hbeta hrho s a d hd
  exact hasDerivWithinAt_cavityFixedRowPhysicalCurveCovariance_zero_of_heat_data
    hn beta rho hbeta hrho s a d hd l r hl.le hband hZ hZf hZg hZh

theorem derivWithin_cavityFixedRowPhysicalCurveCovariance_zero
    (hn : 0 < n) (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc (0 : ℝ) 1) (s : RSBScheme k) (a : ℝ)
    (d : ℕ) (hd : d ≤ k+2) :
    let D0 := followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl, zero_le_one⟩
    derivWithin (cavityFixedRowPhysicalCurveCovariance (n := n) beta rho hbeta hrho s a d)
      (Icc (0 : ℝ) 1) 0 =
      followupCavityAlpha n beta rho / (2*(n : ℝ)) *
        ∑ i : Fin n, fderiv ℝ (fderiv ℝ (cavityFixedRowCovariance D0 s a d)) 0
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  simpa only [cavityRowHessianTrace] using
    (hasDerivWithinAt_cavityFixedRowPhysicalCurveCovariance_zero hn beta rho hbeta hrho s a d hd).derivWithin
      ((uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) 0 (by simp))

theorem derivWithin_cavityFixedRowPhysicalCurveCovariance_eq_fixed_last
    (hn : 0 < n) (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc (0 : ℝ) 1) (s : RSBScheme k) (a : ℝ)
    (d : ℕ) (hd : d ≤ k+2) :
    derivWithin (cavityFixedRowPhysicalCurveCovariance (n := n) beta rho hbeta hrho s a d)
      (Icc (0 : ℝ) 1) 0 =
      derivWithin (fun u => cavityFixedRowVarianceCovariance (n := n) beta rho hbeta hrho s a d
        (followupCavityAlpha n beta rho*u/(n : ℝ))) (Icc (0 : ℝ) 1) 0 := by
  rw [derivWithin_cavityFixedRowPhysicalCurveCovariance_zero hn beta rho hbeta hrho s a d hd,
    derivWithin_cavityFixedRowVarianceCovariance_zero beta rho hbeta hrho s a d hd]

end QuantitativeFollowup
