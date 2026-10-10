module
public import QuantitativeFollowup.AffineProfileCurve
public import QuantitativeFollowup.RootPushedSegment

@[expose] public section

/-! Genuine functional endpoints, minimum and convexity for the actual
pushed root segment. The endpoint cost is derived by the actual first
variation, not supplied as part of the segment data. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem root_pushed_curve_endpoint_budget (n : ℕ) (hn : 0 < n)
    (P : ℝ → Paper.ParisiMeasure) (bar ν : Paper.ParisiMeasure)
    (beta lam rho q eta : ℝ) (hbeta : 0 < beta)
    (hlam : lam ∈ Icc (0 : ℝ) beta) (hrho : 0 < rho)
    (hq : q ∈ Ioc (0 : ℝ) (1/4)) (heta : 0 ≤ eta)
    (hFloor : ∀theta∈Icc (0 : ℝ) 1, P theta ∈ scalarFloor (lam/beta))
    (hProfile : ∀theta∈Icc (0 : ℝ) 1, ∀x : ℝ,
      beta*parisiCDF (P theta) x=beta*parisiCDF bar x+
        theta*concentratingPushedDirection bar ν beta (q/4) (q/2)
          (rootConcentratingStep rho q eta) x)
    (hnearbar : followupEnergyFunctional n beta lam rho bar ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta/12)
    (hnearν : followupEnergyFunctional n beta lam rho ν ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun theta => followupEnergyFunctional n beta lam rho (P theta)) ∧
    ContinuousOn (fun theta => followupEnergyFunctional n beta lam rho (P theta)) (Icc (0 : ℝ) 1) ∧
    (∀theta∈Icc (0 : ℝ) 1, followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le ≤
      followupEnergyFunctional n beta lam rho (P theta)) ∧
    followupEnergyFunctional n beta lam rho (P 0) ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta/12 ∧
    followupEnergyFunctional n beta lam rho (P 1) ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta+45*eta/(4*q) := by
  have hZero : P 0=bar := by
    apply FRSB.eq_of_parisiCDF_ae_eq
    apply Filter.Eventually.of_forall
    intro x
    have hp := hProfile 0 (by norm_num) x
    simp only [zero_mul,add_zero] at hp
    nlinarith
  have hOne : ∀x : ℝ, beta*parisiCDF (P 1) x=beta*parisiCDF ν x-
      rootConcentratingStep rho q eta*concentratingIntervalIncrement (q/4) (q/2) x := by
    intro x
    have hp := hProfile 1 (by norm_num) x
    dsimp only [concentratingPushedDirection] at hp
    linarith
  have hCost := concentrating_admissible_cost_le hn ν (P 1) beta lam rho (q/4) (q/2)
    (rootConcentratingStep rho q eta) hbeta hlam.1 hrho (by linarith [hq.1])
    (by linarith [hq.2]) (half_pos hq.1) (by unfold rootConcentratingStep; positivity [hq.1]) hOne
  have hTerm : rho*rootConcentratingStep rho q eta/2=45*eta/(4*q) := by
    unfold rootConcentratingStep
    field_simp [hq.1.ne']
    ring
  rw [hTerm] at hCost
  refine ⟨convexOn_affine_profile_functional n P bar beta lam rho _ hbeta hlam.1 hrho.le hProfile,
    continuousOn_affine_profile_functional n hn P bar beta lam rho _ hbeta hrho.le hProfile,
    (fun theta htheta => followupEnergyMinimum_le hn beta lam rho hbeta hlam.2 hrho.le
      (P theta) (hFloor theta htheta)),?_,?_⟩
  · rwa [hZero]
  · linarith

end QuantitativeFollowup
