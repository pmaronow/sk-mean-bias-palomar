module
public import QuantitativeFollowup.SmallIntervalProposition
public import QuantitativeFollowup.FoundationTrialBudget

@[expose] public section

/-! Actual clipped-trial budgets and the genuine native interpolation
integral for the general-tilt comparison error. -/
noncomputable section
open Set MeasureTheory Paper FRSB QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 2200000

 theorem fourTermBudget_energyMinimum_eq (n : ℕ) (hn : 0<n) (β lam rho : ℝ)
    (hβ : 0<β) (hlam : lam ≤ β) (hrho : 0 ≤ rho) :
    followupEnergyMinimum n hn β lam rho hβ hlam hrho=
      vectorInterpolationMinimum n β (lam/β) (1-rho)/β := by
  let μ:=vectorMeasureMinimizer n hn β (1-rho) (lam/β) (by linarith) ((div_le_one hβ).mpr hlam)
  have hμ:=vectorMeasureMinimizer_mem n hn β (1-rho) (lam/β) (by linarith) ((div_le_one hβ).mpr hlam)
  have hmin:=vectorMeasureMinimizer_minimal n hn β (1-rho) (lam/β) (by linarith) ((div_le_one hβ).mpr hlam)
  have he:=vectorInterpolationMinimum_eq_of_minimizer hn μ β (lam/β) (1-rho)
    ((div_le_one hβ).mpr hlam) (by linarith) hμ hmin
  change vectorMeasureFunctional n μ β (1-rho) (lam/β)/β=_
  rw [he]

 theorem fourTermBudget_actual_trial (β : ℝ) (hβ : 1<β) :
    ∃L lambda0 : ℝ,1 ≤ L ∧ lambda0∈Ioc (0:ℝ) 1 ∧ ∃h0β : lambda0 ≤ β/4,
      ∀n : ℕ,∀hn : 0<n,∀lam : ℝ,∀hlam : lam∈Ioc (0:ℝ) lambda0,
      ∀rho : ℝ,∀hrho : rho∈Ioc (0:ℝ) 1,
      smallIntervalTrialGap n hn β lam rho (zero_lt_one.trans hβ)
        ⟨hlam.1.le,by linarith [hlam.2.trans h0β]⟩ hrho.1.le ≤ 
        energyComparisonError n β lam+L*lam^5 := by
  obtain ⟨L,lambda0,hL,h0,h0β,hTrial⟩:=foundation_trial_budget_complete β hβ
  have hβp : 0<β:=zero_lt_one.trans hβ
  refine ⟨L,lambda0,hL,h0,h0β,?_⟩
  intro n hn lam hlam rho hrho
  have hlamβ : lam ≤ β:=by linarith [hlam.2.trans h0β]
  obtain ⟨hs,hTrial⟩:=hTrial (parisiMinimizer β 0) (isParisiMinimizer_selected β 0)
    n hn lam hlam (1-rho) ⟨by linarith [hrho.2],by linarith [hrho.1]⟩
  have hb:=hTrial.2
  rw [←fourTermBudget_energyMinimum_eq n hn β lam rho hβp hlamβ hrho.1.le] at hb
  change smallIntervalTrialGap n hn β lam rho hβp ⟨hlam.1.le,hlamβ⟩ hrho.1.le ≤ _
  exact hb

 theorem fourTermBudget_native_envelope (n : ℕ) (hn : 0<n) (β lam : ℝ)
    (hβ : 0<β) (hs : lam/β∈Ioo (0:ℝ) 1) :
    IntervalIntegrable (smallIntervalDefect n β lam) volume 0 1 ∧
      4*energyComparisonError n β lam=(∫rho in (0:ℝ)..1,smallIntervalDefect n β lam rho) := by
  have henv:=vectorInterpolationMinimum_integral n hn β (lam/β) hs hβ.ne'
  refine ⟨smallIntervalDefect_intervalIntegrable n hn β lam hβ hs,?_⟩
  change 4*energyComparisonError n β lam=(∫rho in (0:ℝ)..1,β*optimizedVectorInterpolationDefect n β (lam/β) (1-rho))
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (optimizedVectorInterpolationDefect n β (lam/β)) 1]
  norm_num only [sub_self,sub_zero]
  rw [energyComparisonError_eq_fractional_gap n β lam hβ.ne',henv.2]
  field_simp [hβ.ne']
  <;> ring

end QuantitativeFollowup
