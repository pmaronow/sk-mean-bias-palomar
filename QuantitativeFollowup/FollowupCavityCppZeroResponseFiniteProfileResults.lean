module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteResults
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFloorObservation

@[expose] public section

/-! Every observation of an actual finite profile has the printed
zero-response formula after an exact floor-preserving refinement. This
uses the proven physical response on the refined scheme itself. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open FourPapersCommon.FiniteStreamingPolynomials
open SpinGlass.Targets
variable {n : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

theorem native_cpp_firstJet_finite_profile_zero_eq_linear_response
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (hμ : (μ:Measure Paper.Overlap).support.Finite)
    (a : ℝ) (ha : 0≤a) (hfloor : a≤Paper.parisiCDF μ 0) (p : Paper.Overlap) :
    withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) 1 0=
      followupCavityLinearResponseRightSide n β ρ hβ hρ μ a p:=by
  obtain ⟨K,s,d,hd,hs,hszero,has,hp⟩:=
    exists_cavity_zero_response_finite_floor_observation μ hμ a hfloor p
  have he:=native_cpp_firstJet_scheme_zero_eq_linear_response hn β ρ hβ hρ s a ha has hszero d hd
  dsimp only at he
  rw [hs,hp] at he
  exact he

end QuantitativeFollowup
