module
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import QuantitativeFollowup.FollowupCavityFixedRowHeatFactories
public import QuantitativeFollowup.FollowupCavityMixtureScaledCovariance
public import QuantitativeFollowup.FollowupCavityFixedRowSymmetry

@[expose] public section

/-! The literal deterministic-row covariance response. The Z-weighted
mixture, genuine C2 numerator factories and actual reflection discharge
all analytic inputs before evaluating the right row-variance derivative. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem hasDerivWithinAt_cavityFixedRowVarianceCovariance_zero
    (beta rho : ℝ) (hbeta : 0<beta) (hrho : rho∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d ≤ k+2)
    (scale : ℝ) (hscale : 0 ≤ scale) :
    let D0:=followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩
    HasDerivWithinAt (fun u=>cavityFixedRowVarianceCovariance (n:=n) beta rho hbeta hrho s a d (scale*u))
      (scale/2*cavityRowHessianTrace (cavityFixedRowCovariance D0 s a d)) (Ici (0:ℝ)) 0 := by
  dsimp only
  let D0:=followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩
  obtain ⟨hZ⟩:=cavityFixedRowNormalizer_heat_data D0 s a
  obtain ⟨hF⟩:=cavityFixedRowLastMean_weighted_heat_data D0 s a d hd
  obtain ⟨hG⟩:=cavityFixedRowRestMean_weighted_heat_data D0 s a d hd
  obtain ⟨hH⟩:=cavityFixedRowProductMean_weighted_heat_data D0 s a d hd
  have hh:=hasDerivWithinAt_cavityRowWeightedCovariance_scaled_zero
    (cavityFixedRowNormalizer D0 s a) (cavityFixedRowLastMean D0 s a d)
    (cavityFixedRowRestMean D0 s a d) (cavityFixedRowProductMean D0 s a d)
    hZ ((contDiff_cavityFixedRowLastMean D0 s a d hd).of_le (by simp))
    ((contDiff_cavityFixedRowRestMean D0 s a d hd).of_le (by simp))
    ((contDiff_cavityFixedRowProductMean D0 s a d hd).of_le (by simp)) hF hG hH
    (cavityFixedRowNormalizer_pos D0 s a 0)
    (fderiv_cavityFixedRowNormalizer_zero beta rho hbeta hrho s a)
    (fderiv_cavityFixedRowLastSquare_integral_zero beta rho hbeta hrho s a d) scale hscale
  exact hh.congr_of_mem (fun u hu=>
    cavityFixedRowVarianceCovariance_eq_weighted beta rho hbeta hrho s a d (scale*u)
      (mul_nonneg hscale hu)) (by simp)

theorem derivWithin_cavityFixedRowVarianceCovariance_zero
    (beta rho : ℝ) (hbeta : 0<beta) (hrho : rho∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d ≤ k+2) :
    let D0:=followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩
    derivWithin (fun u=>cavityFixedRowVarianceCovariance (n:=n) beta rho hbeta hrho s a d
      (followupCavityAlpha n beta rho*u/(n:ℝ))) (Icc (0:ℝ) 1) 0=
      followupCavityAlpha n beta rho/(2*(n:ℝ))*
        ∑i : Fin n,fderiv ℝ (fderiv ℝ (cavityFixedRowCovariance D0 s a d)) 0
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  dsimp only
  have hs : 0 ≤ followupCavityAlpha n beta rho/(n:ℝ) :=
    div_nonneg (followupCavityAlpha_nonneg n beta rho hrho.2) (Nat.cast_nonneg n)
  have hh:=((hasDerivWithinAt_cavityFixedRowVarianceCovariance_zero (n := n) beta rho hbeta hrho s a d hd
    (followupCavityAlpha n beta rho/(n:ℝ)) hs).mono (fun _ hx=>hx.1)).derivWithin
      ((uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1)) 0 (by simp))
  simpa only [cavityRowHessianTrace,div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_comm,mul_left_comm] using hh

end QuantitativeFollowup
