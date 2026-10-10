module
public import QuantitativeFollowup.FollowupCavityCppNativeRegularity

@[expose] public section

/-! Actual derivatives of every native Cpp jet on the closed interval. -/
noncomputable section
open Set
open scoped ContDiff
namespace QuantitativeFollowup
open FourPapersCommon
open FourPapersCommon.FiniteStreamingPolynomials
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem contDiffOn_followupCavityCppFunction_withinJet (hn : 0<n) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap) (r : ℕ) :
    ContDiffOn ℝ ∞ (withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) r)
      (Icc (0:ℝ) 1) := by
  induction r with
  | zero => exact contDiffOn_followupCavityCppFunction hn β ρ hβ hρ μ a ha hfloor p
  | succ r ih => exact ih.derivWithin uniqueDiffOn_Icc_zero_one (by simp)

theorem hasDerivWithinAt_followupCavityCppFunction_withinJet (hn : 0<n) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap)
    (r : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) r)
      (withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) (r+1) u)
        (Icc (0:ℝ) 1) u :=
  ((contDiffOn_followupCavityCppFunction_withinJet hn β ρ hβ hρ μ a ha hfloor p r).differentiableOn
    (by simp) u hu).hasDerivWithinAt

end QuantitativeFollowup
