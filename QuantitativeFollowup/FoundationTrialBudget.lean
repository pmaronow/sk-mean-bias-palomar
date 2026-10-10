module
public import QuantitativeFollowup.FoundationScalarTrialConstants

@[expose] public section

/-! Follow-up Lemma 2.5 with its actual clipped scalar trial and attained
vector minimum, and temperature-only constants. -/
noncomputable section
open Set MeasureTheory Paper FRSB QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000

theorem foundation_trial_budget_complete (β : ℝ) (hβ : 1<β) :
    ∃L lambda0 : ℝ,1≤ L ∧ lambda0∈Ioc (0:ℝ) 1 ∧ lambda0≤β/4 ∧
      ∀μ,IsParisiMinimizer β 0 μ→∀n : ℕ,0<n→∀lam∈Ioc (0:ℝ) lambda0,
      ∀t∈Icc (0:ℝ) 1,∃hs : lam/β∈Icc (0:ℝ) 1,
        let ν:=scalarClippedTrialMeasure (lam/β) hs μ
        0≤ responseEnergyFunctional n ν β t lam-vectorInterpolationMinimum n β (lam/β) t/β ∧
        responseEnergyFunctional n ν β t lam-vectorInterpolationMinimum n β (lam/β) t/β≤
          energyComparisonError n β lam+L*lam^5 := by
  obtain ⟨L,lambda0,hL,h0,h0β,hdata⟩:=foundation_scalar_trial_constants β hβ
  have hβp:0<β:=zero_lt_one.trans hβ
  refine ⟨L,lambda0,hL,h0,h0β,?_⟩
  intro μ hmin n hn lam hlam t ht
  have hlp:0<lam:=hlam.1
  obtain ⟨hs,hν,hzero,hmid,hcost⟩:=hdata μ hmin lam
    ⟨hlam.1.le,by linarith [hlam.2,h0.1]⟩
  let ν:=scalarClippedTrialMeasure (lam/β) hs μ
  have hs':lam/β∈Ioo (0:ℝ) 1:=by
    constructor
    · positivity
    · apply (div_lt_one hβp).2
      have hh:=hlam.2.trans h0β
      linarith
  let μv:=vectorMeasureMinimizer n hn β t (lam/β) ht.2 hs.2
  have hμv:μv∈scalarFloor (lam/β):=vectorMeasureMinimizer_mem n hn β t (lam/β) ht.2 hs.2
  have hminv:∀ρ∈scalarFloor (lam/β),vectorMeasureFunctional n μv β t (lam/β)≤
      vectorMeasureFunctional n ρ β t (lam/β):=vectorMeasureMinimizer_minimal n hn β t (lam/β) ht.2 hs.2
  have hb:=foundation_trial_budget n hn β lam t L hβp hs' ht μv ν hμv hν hminv hzero hcost
  have he:=vectorInterpolationMinimum_eq_of_minimizer hn μv β (lam/β) t hs.2 ht.2 hμv hminv
  refine ⟨hs,?_⟩
  dsimp only
  rw [←he]
  exact hb

end QuantitativeFollowup
