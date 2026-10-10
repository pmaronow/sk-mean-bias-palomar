module
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import QuantitativeFollowup.FollowupCavityMixtureCovariance

@[expose] public section

/-! The physical row covariance has variance scale alpha/n. This scales
the genuine right-zero response without suppressing either quotient term. -/
noncomputable section
open Set
open scoped ContDiff
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1100000

theorem hasDerivWithinAt_cavityRowWeightedCovariance_scaled_zero
    (Z f g h : QuantitativePaper.Field n→ℝ)
    (hZ : CavityRowHeatData Z) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 2 h) (hZf : CavityRowHeatData (fun x=>Z x*f x))
    (hZg : CavityRowHeatData (fun x=>Z x*g x))
    (hZh : CavityRowHeatData (fun x=>Z x*h x))
    (hpos : 0<Z 0) (hZzero : fderiv ℝ Z 0=0) (hfzero : fderiv ℝ f 0=0)
    (scale : ℝ) (hscale : 0 ≤ scale) :
    HasDerivWithinAt (fun u=>cavityRowWeightedAverage Z h (scale*u)-
      cavityRowWeightedAverage Z f (scale*u)*cavityRowWeightedAverage Z g (scale*u))
      (scale/2*cavityRowHessianTrace (fun x=>h x-f x*g x)) (Ici (0:ℝ)) 0 := by
  have hd:=hasDerivWithinAt_cavityRowWeightedCovariance_zero Z f g h hZ hf hg hh
    hZf hZg hZh hpos hZzero hfzero
  have hi : HasDerivWithinAt (fun u : ℝ=>scale*u) scale (Ici (0:ℝ)) 0 := by
    simpa only [mul_one,id_eq] using ((hasDerivAt_id (0:ℝ)).const_mul scale).hasDerivWithinAt
  have hc:=hd.comp_of_eq 0 hi (fun u hu=>mul_nonneg hscale hu) (by simp)
  simpa only [Function.comp_def,mul_zero,mul_assoc,div_eq_mul_inv,mul_comm,mul_left_comm,one_mul] using hc

theorem derivWithin_cavityRowWeightedCovariance_scaled_zero
    (Z f g h : QuantitativePaper.Field n→ℝ)
    (hZ : CavityRowHeatData Z) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 2 h) (hZf : CavityRowHeatData (fun x=>Z x*f x))
    (hZg : CavityRowHeatData (fun x=>Z x*g x))
    (hZh : CavityRowHeatData (fun x=>Z x*h x))
    (hpos : 0<Z 0) (hZzero : fderiv ℝ Z 0=0) (hfzero : fderiv ℝ f 0=0)
    (scale : ℝ) (hscale : 0 ≤ scale) :
    derivWithin (fun u=>cavityRowWeightedAverage Z h (scale*u)-
      cavityRowWeightedAverage Z f (scale*u)*cavityRowWeightedAverage Z g (scale*u))
      (Icc (0:ℝ) 1) 0=scale/2*cavityRowHessianTrace (fun x=>h x-f x*g x) := by
  exact ((hasDerivWithinAt_cavityRowWeightedCovariance_scaled_zero Z f g h hZ hf hg hh
    hZf hZg hZh hpos hZzero hfzero scale hscale).mono (fun _ hx=>hx.1)).derivWithin
      ((uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1)) 0 (by simp))

end QuantitativeFollowup
