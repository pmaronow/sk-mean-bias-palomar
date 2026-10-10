module
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import QuantitativeFollowup.FollowupCavityFixedRowPhysicalCurve
public import QuantitativeFollowup.FollowupCavityFixedRowHeatFactories
public import QuantitativeFollowup.FollowupCavityFixedRowSymmetry
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVarianceCovariance

@[expose] public section

/-! Actual physical row response once the four genuine local heat-data
factories are supplied. The zero-row product identity, row symmetry, and
the identification with the original moving-variance curve are proved
from their actual model laws. No response or baseline derivative is an input. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem hasDerivWithinAt_cavityFixedRowPhysicalCurveCovariance_zero_of_heat_data
    (hn : 0 < n) (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc (0 : ℝ) 1) (s : RSBScheme k) (a : ℝ)
    (d : ℕ) (hd : d ≤ k+2) (l r : ℝ) (hl : 0 ≤ l)
    (hband : followupCavityD n beta rho ∈ Ioo l r)
    (hZ : CavityMovingRowHeatData (cavityFixedRowMovingNormalizer (n := n) beta rho hbeta hrho s a) l r)
    (hZf : CavityMovingRowHeatData (fun z =>
      cavityFixedRowMovingNormalizer (n := n) beta rho hbeta hrho s a z *
        cavityFixedRowMovingLastMean (n := n) beta rho hbeta hrho s a d z) l r)
    (hZg : CavityMovingRowHeatData (fun z =>
      cavityFixedRowMovingNormalizer (n := n) beta rho hbeta hrho s a z *
        cavityFixedRowMovingRestMean (n := n) beta rho hbeta hrho s a d z) l r)
    (hZh : CavityMovingRowHeatData (fun z =>
      cavityFixedRowMovingNormalizer (n := n) beta rho hbeta hrho s a z *
        cavityFixedRowMovingProductMean (n := n) beta rho hbeta hrho s a d z) l r) :
    let D0 := followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl, zero_le_one⟩
    HasDerivWithinAt (cavityFixedRowPhysicalCurveCovariance (n := n) beta rho hbeta hrho s a d)
      (followupCavityAlpha n beta rho / (2*(n : ℝ)) *
        cavityRowHessianTrace (cavityFixedRowCovariance D0 s a d)) (Icc (0 : ℝ) 1) 0 := by
  dsimp only
  let D0 := followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl, zero_le_one⟩
  let Z := cavityFixedRowMovingNormalizer (n := n) beta rho hbeta hrho s a
  let f := cavityFixedRowMovingLastMean (n := n) beta rho hbeta hrho s a d
  let g := cavityFixedRowMovingRestMean (n := n) beta rho hbeta hrho s a d
  let h := cavityFixedRowMovingProductMean (n := n) beta rho hbeta hrho s a d
  let b0 := followupCavityD n beta rho
  have hpos : 0 < Z (b0,0) := by
    simpa only [Z,b0,cavityFixedRowMovingNormalizer,
      cavityFixedRowPositiveVarianceModel_at_physical] using
      cavityFixedRowNormalizer_pos D0 s a 0
  have hf : ContDiff ℝ 2 (fun x => f (b0,x)) := by
    simpa only [f,b0,cavityFixedRowMovingLastMean,
      cavityFixedRowPositiveVarianceModel_at_physical] using
      (contDiff_cavityFixedRowLastMean D0 s a d hd).of_le (by simp)
  have hg : ContDiff ℝ 2 (fun x => g (b0,x)) := by
    simpa only [g,b0,cavityFixedRowMovingRestMean,
      cavityFixedRowPositiveVarianceModel_at_physical] using
      (contDiff_cavityFixedRowRestMean D0 s a d hd).of_le (by simp)
  have hh : ContDiff ℝ 2 (fun x => h (b0,x)) := by
    simpa only [h,b0,cavityFixedRowMovingProductMean,
      cavityFixedRowPositiveVarianceModel_at_physical] using
      (contDiff_cavityFixedRowProductMean D0 s a d hd).of_le (by simp)
  have hZzero : fderiv ℝ (fun x => Z (b0,x)) 0 = 0 := by
    simpa only [Z,b0,cavityFixedRowMovingNormalizer,
      cavityFixedRowPositiveVarianceModel_at_physical] using
      fderiv_cavityFixedRowNormalizer_zero beta rho hbeta hrho s a
  have hfzero : fderiv ℝ (fun x => f (b0,x)) 0 = 0 := by
    simpa only [f,b0,cavityFixedRowMovingLastMean,cavityFixedRowLastMean,
      cavityFixedRowPositiveVarianceModel_at_physical] using
      fderiv_cavityFixedRowLastSquare_integral_zero beta rho hbeta hrho s a d
  have hbase : ∀ b ∈ Ioo l r, h (b,0) = f (b,0) * g (b,0) := by
    intro b hb
    have hbp : 0 < b := hl.trans_lt hb.1
    have hc := cavityFixedRowCovariance_lastVariance_zero s n beta rho hbeta hrho b hbp a d hd
    simpa only [h,f,g,cavityFixedRowMovingProductMean,cavityFixedRowMovingLastMean,
      cavityFixedRowMovingRestMean,cavityFixedRowPositiveVarianceModel_eq beta rho hbeta hrho b hbp,
      cavityFixedRowProductMean,cavityFixedRowLastMean,cavityFixedRowRestMean,sub_eq_zero] using hc
  have hc := hasDerivWithinAt_cavityMovingRowWeightedCovariance_zero Z f g h l r b0 (n : ℝ)
    hZ hZf hZg hZh hband hpos hf hg hh hZzero hfzero hbase
  have hs : 0 ≤ followupCavityAlpha n beta rho / (n : ℝ) :=
    div_nonneg (followupCavityAlpha_nonneg n beta rho hrho.2) (Nat.cast_nonneg n)
  have hi : HasDerivWithinAt (fun u : ℝ => followupCavityAlpha n beta rho / (n : ℝ)*u)
      (followupCavityAlpha n beta rho / (n : ℝ)) (Icc (0 : ℝ) 1) 0 := by
    simpa only [mul_one,id_eq] using
      ((hasDerivAt_id (0 : ℝ)).const_mul (followupCavityAlpha n beta rho / (n : ℝ))).hasDerivWithinAt
  have ht := hc.comp_of_eq 0 hi (fun u hu => mul_nonneg hs hu.1) (by simp)
  have hjet : (fun x => h (b0,x)-f (b0,x)*g (b0,x)) = cavityFixedRowCovariance D0 s a d := by
    simp only [h,f,g,b0,cavityFixedRowMovingProductMean,cavityFixedRowMovingLastMean,
      cavityFixedRowMovingRestMean,cavityFixedRowPositiveVarianceModel_at_physical]
    rfl
  rw [hjet] at ht
  have ht' : HasDerivWithinAt (fun u => cavityMovingRowWeightedCovariance Z f g h b0 (n : ℝ)
      (followupCavityAlpha n beta rho / (n : ℝ)*u))
      (followupCavityAlpha n beta rho / (2*(n : ℝ)) *
        cavityRowHessianTrace (cavityFixedRowCovariance D0 s a d)) (Icc (0 : ℝ) 1) 0 := by
    simpa only [Function.comp_def,mul_zero,mul_assoc,div_eq_mul_inv,mul_inv_rev,mul_comm,mul_left_comm,one_mul] using ht
  exact ht'.congr_of_mem (fun u hu =>
    cavityFixedRowPhysicalCurveCovariance_eq_moving hn beta rho hbeta hrho s a d u hu)
    (by simp)

end QuantitativeFollowup
