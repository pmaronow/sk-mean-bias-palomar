module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseCheckpoint
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceNativeProfile
public import QuantitativeFollowup.StableIntervalFromCavity

@[expose] public section

/-! Unconditional native stable-profile and four-term bounds. The actual
zero response is supplied by its separately audited proof, while the
upper atom, cubic remainder and stability inputs are discharged internally. -/
noncomputable section
open Set MeasureTheory Paper FRSB QuantitativePaper
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem followup_cavity_stable_defect_actual_minimizer
    (N : ℕ) (hN : 2 ≤ N) (β : ℝ) (hβ : 1 < β)
    (μ : Paper.ParisiMeasure) (lam rho : ℝ)
    (hlam : lam∈Ioc (0:ℝ) (min 1 (β/4))) (hrho : rho∈Ioc (0:ℝ) 1)
    (hNr : (N:ℝ)⁻¹ ≤ rho) (hμ : μ∈scalarFloor (lam/β))
    (hmin : ∀ν∈scalarFloor (lam/β),
      vectorMeasureFunctional N μ β (1-rho) (lam/β) ≤
        vectorMeasureFunctional N ν β (1-rho) (lam/β))
    (hstable : scalarOperatorStabilityError β μ (followupScalarCoefficient N β rho) ≤ rho/4) :
    β*vectorInterpolationDefect (n:=N) μ (lam/β) β (1-rho) (by linarith [hrho.1]) ≤
      followupCavityNativeStableDefectConstant β*(Real.log (2+(N:ℝ)))^2/
        ((N:ℝ)*lam*rho^2) := by
  have hb : 0 < β := zero_lt_one.trans hβ
  have hn : 0 < N-1 := by omega
  have ha : lam/β∈Ioc (0:ℝ) (1/2) := by
    refine ⟨div_pos hlam.1 hb,(div_le_iff₀ hb).mpr ?_⟩
    linarith [hlam.2.trans (min_le_right 1 (β/4))]
  have ha01 : lam/β∈Icc (0:ℝ) 1 := ⟨ha.1.le,by linarith [ha.2]⟩
  have hResponse := followupCavityCpp_zero_response_ae (N-1) hn β rho hb hrho μ (lam/β) ha01 hμ
  exact followup_cavity_stable_defect_of_zero_response N hN β hβ μ lam rho
    hlam hrho hNr hμ hmin hstable hResponse

theorem followup_actual_stable_cavity_profile_bound (β : ℝ) (hβ : 1 < β) :
    StableCavityProfileBound β (followupCavityNativeStableDefectConstant β) := by
  intro N hN μ lam rho hlam hrho hμ hmin hNr hstable
  exact followup_cavity_stable_defect_actual_minimizer N hN β hβ μ lam rho
    hlam hrho hNr hμ hmin hstable

theorem followup_actual_stable_interval_integral (β : ℝ) (hβ : 1 < β) :
    ∃ Cst Ct : ℝ,1 ≤ Cst ∧ 0 < Ct ∧
      FourTermStableIntegralHypothesis β hβ (min 1 (β/4)) Cst Ct :=
  stable_interval_integral_of_cavity_profile_bound β hβ
    (followupCavityNativeStableDefectConstant β)
    (followupCavityNativeStableDefectConstant_pos β hβ).le
    (followup_actual_stable_cavity_profile_bound β hβ)

theorem followup_actual_four_term_budget (β : ℝ) (hβ : 1 < β) :
    ∃ C L lambda0 : ℝ,0 < C ∧ 1 ≤ L ∧ lambda0∈Ioc (0:ℝ) 1 ∧ lambda0 ≤ β/4 ∧
      ∀ N : ℕ,∀ hN : 2 ≤ N,∀ lam∈Icc ((N:ℝ)⁻¹) lambda0,
      0 ≤ energyComparisonError N β lam ∧
      energyComparisonError N β lam ≤ C*fourTermBudgetRate (N:ℝ) lam := by
  obtain ⟨Cst,Ct,hCst,hCt,hIntegral⟩ := followup_actual_stable_interval_integral β hβ
  exact four_term_budget_of_stable_integral β hβ (min 1 (β/4)) Cst Ct
    ⟨lt_min zero_lt_one (div_pos (zero_lt_one.trans hβ) (by norm_num)),min_le_left _ _⟩
    (min_le_right _ _) hCst hCt.le hIntegral

end QuantitativeFollowup
