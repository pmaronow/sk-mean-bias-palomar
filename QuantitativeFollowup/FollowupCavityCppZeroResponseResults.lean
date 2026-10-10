module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteProfileResults
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeFirstJetLimit
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileLimitCheckpoint

@[expose] public section

/-! The actual native diagonal-linear response follows by passing the
genuine finite physical identities through atom-preserving profiles.
The native jet and every term of the constructed right side have their
own actual convergence theorems. No response premise is introduced. -/
noncomputable section
open Set Filter MeasureTheory FourPapersCommon QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon.FiniteStreamingPolynomials
variable {n : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem followupCavityCpp_zero_response (n : ℕ) (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (p : Paper.Overlap) :
    withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) 1 0=
      followupCavityLinearResponseRightSide n β ρ hβ hρ μ a p:=by
  have hf:a≤Paper.parisiCDF μ 0:=by
    rw [mem_scalarFloor_iff,zeroMass_eq_parisiCDF_zero] at hfloor
    exact hfloor
  let S:Finset Paper.Overlap:={zeroOverlap,p}
  have hzero:zeroOverlap∈S:=by simp [S]
  have hleft:=tendsto_followupCavityCpp_firstJet_zero_preserving hn β ρ hβ hρ μ S hzero a ha hf p
  have hright:=tendsto_followupCavityLinearResponseRightSide_prescribed
    n hn β ρ hβ hρ μ p a ha hfloor
  have he (N : ℕ):withinJet (followupCavityCppFunction n β ρ hβ hρ
      (FRSB.preservingMeasure μ S N) a p) (Icc (0:ℝ) 1) 1 0=
      followupCavityLinearResponseRightSide n β ρ hβ hρ (FRSB.preservingMeasure μ S N) a p:=by
    have hfN:a≤Paper.parisiCDF (FRSB.preservingMeasure μ S N) 0:=by
      change a ≤ Paper.parisiCDF (FRSB.preservingMeasure μ S N) (zeroOverlap:ℝ)
      rw [FRSB.preservingMeasure_cdf_mass μ S N zeroOverlap hzero]
      exact hf
    exact native_cpp_firstJet_finite_profile_zero_eq_linear_response hn β ρ hβ hρ
      (FRSB.preservingMeasure μ S N) (FRSB.finite_support_preservingMeasure μ S N) a ha.1 hfN p
  exact tendsto_nhds_unique hleft (hright.congr' (.of_forall fun N=>(he N).symm))

theorem followupCavityCpp_zero_response_ae (n : ℕ) (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) :
    (fun p=>withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) 1 0)
      =ᵐ[parisiFreeMeasure μ a] followupCavityLinearResponseRightSide n β ρ hβ hρ μ a:=
  .of_forall (followupCavityCpp_zero_response n hn β ρ hβ hρ μ a ha hfloor)

end QuantitativeFollowup
