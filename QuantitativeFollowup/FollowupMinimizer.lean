module
public import QuantitativeFollowup.PartialLocalizationProfile
public import QuantitativeFollowup.ConcentratingAdmissibleCost

@[expose] public section

/-! The actual minimizing profile in energy normalization, and the exact
partial-regularization near-minimum budget used in root localization. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

def followupMinimizer (n : ℕ) (hn : 0 < n) (beta lam rho : ℝ)
    (hbeta : 0 < beta) (hlam : lam ≤ beta) (hrho : 0 ≤ rho) : Paper.ParisiMeasure :=
  vectorMeasureMinimizer n hn beta (1-rho) (lam/beta) (by linarith) ((div_le_one hbeta).mpr hlam)

theorem followupMinimizer_mem_floor (n : ℕ) (hn : 0 < n) (beta lam rho : ℝ)
    (hbeta : 0 < beta) (hlam : lam ≤ beta) (hrho : 0 ≤ rho) :
    followupMinimizer n hn beta lam rho hbeta hlam hrho ∈ scalarFloor (lam/beta) :=
  vectorMeasureMinimizer_mem n hn beta (1-rho) (lam/beta) (by linarith) ((div_le_one hbeta).mpr hlam)

theorem followupMinimizer_value (n : ℕ) (hn : 0 < n) (beta lam rho : ℝ)
    (hbeta : 0 < beta) (hlam : lam ≤ beta) (hrho : 0 ≤ rho) :
    followupEnergyFunctional n beta lam rho (followupMinimizer n hn beta lam rho hbeta hlam hrho)=
      followupEnergyMinimum n hn beta lam rho hbeta hlam hrho := rfl

theorem followupMinimizer_partial_budget (n : ℕ) (hn : 0 < n) (beta lam rho q h eta : ℝ)
    (hbeta : 0 < beta) (hlam : lam ∈ Icc (0 : ℝ) beta)
    (hrho : rho ∈ Icc (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) (hh : h ∈ Ioc (0 : ℝ) (1-q))
    (hbudget : rho*(beta*(parisiFreeMeasure (followupMinimizer n hn beta lam rho hbeta hlam.2 hrho.1)
      (lam/beta)).real (overlapBelow q))*h^2 ≤ eta) :
    followupEnergyFunctional n beta lam rho
      (partialReflectedParisiMeasure (followupMinimizer n hn beta lam rho hbeta hlam.2 hrho.1)
        (lam/beta) q h ⟨div_nonneg hlam.1 hbeta.le,(div_le_one hbeta).mpr hlam.2⟩ hh.1) ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.1+eta/12 := by
  have hc := partial_reflected_followup_energy_cost_le n hn beta hbeta _ lam rho q h
    hlam hrho (followupMinimizer_mem_floor n hn beta lam rho hbeta hlam.2 hrho.1) hq hh
  rw [followupMinimizer_value] at hc
  linarith

end QuantitativeFollowup
