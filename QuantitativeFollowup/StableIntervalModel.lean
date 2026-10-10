module
public import QuantitativeFollowup.StableIntervalCutoff
public import QuantitativeFollowup.ScalarMinimizerStability
public import QuantitativeFollowup.FoundationScalarTrialConstants
public import QuantitativePaper.ShortVarianceMeanUniform
public import QuantitativeFollowup.FollowupMinimizer

@[expose] public section

/-! The stable cutoff applied to the actual finite-system comparison error
and every actual constrained minimizer. Trial and stability bounds are
proved model results, with constants depending only on temperature. -/
noncomputable section
open Set MeasureTheory Paper FRSB QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 2000000

def stableIntervalTrialBudget (n : ℕ) (β lam L : ℝ) : ℝ :=
  energyComparisonError n β lam+L*lam^5

theorem stable_interval_actual_minimizers (β : ℝ) (hβ : 1 < β) :
    ∃ L lambda0 C : ℝ, 1 ≤ L ∧ lambda0 ∈ Ioc (0:ℝ) 1 ∧
      lambda0 ≤ β/4 ∧ 1 ≤ C ∧
      ∀ n : ℕ, ∀ hn : 2 ≤ n, ∀ lam : ℝ,
      lam ∈ Icc ((n:ℝ)⁻¹) lambda0 →
      let eta := stableIntervalTrialBudget n β lam L
      let rho0 := stableIntervalCutoff C eta
      lam^5 ≤ eta ∧ 0 < rho0 ∧ min 1 (12*C*lam^((5:ℝ)/7)) ≤ rho0 ∧
      rho0 ≤ 12*C*eta^((1:ℝ)/7) ∧
      (rho0 < 1 → ∀ rho ∈ Icc rho0 1, ∀ μ : Paper.ParisiMeasure,
        μ ∈ scalarFloor (lam/β) →
        (∀ ν ∈ scalarFloor (lam/β),
          vectorMeasureFunctional n μ β (1-rho) (lam/β) ≤
            vectorMeasureFunctional n ν β (1-rho) (lam/β)) →
        0 < rho ∧ (n:ℝ)⁻¹ ≤ rho ∧
        0 ≤ scalarOperatorStabilityError β μ (followupScalarCoefficient n β rho) ∧
        scalarOperatorStabilityError β μ (followupScalarCoefficient n β rho) ≤ rho/4) := by
  have hb : 0 < β := zero_lt_one.trans hβ
  obtain ⟨L,lambda0,hL,h0,h0β,htrial⟩ := foundation_scalar_trial_constants β hβ
  obtain ⟨C,hC,hstable⟩ := scalar_minimizer_stability β hβ
  refine ⟨L,lambda0,C,hL,h0,h0β,hC,?_⟩
  intro n hn lam hlam
  have hnp : 0 < n := by omega
  have hNr : 0 < (n:ℝ) := by exact_mod_cast hnp
  have hlp : 0 < lam := (inv_pos.mpr hNr).trans_le hlam.1
  have hl1 : lam ≤ 1 := hlam.2.trans h0.2
  have hlβ : lam ≤ β := by linarith [hlam.2.trans h0β]
  have hs : lam/β ∈ Ioo (0:ℝ) 1 := by
    refine ⟨div_pos hlp hb,(div_lt_one hb).mpr ?_⟩
    linarith [hlam.2.trans h0β]
  have he : 0 ≤ energyComparisonError n β lam :=
    energyComparisonError_nonneg n hnp β hb lam hs
  let eta := stableIntervalTrialBudget n β lam L
  have heta : lam^5 ≤ eta := by
    have hh := mul_le_mul_of_nonneg_right hL (pow_nonneg hlp.le 5)
    dsimp only [eta,stableIntervalTrialBudget]
    linarith
  have hη : 0 ≤ eta := (pow_nonneg hlp.le 5).trans heta
  have hbounds := stableIntervalCutoff_bounds C eta lam hC hlp heta
  dsimp only
  refine ⟨heta,hbounds.1,hbounds.2.1,hbounds.2.2,?_⟩
  intro hcut rho hr μ hμ hmin
  have harith := stableIntervalCutoff_stability C eta lam ((n:ℝ)⁻¹) rho
    hC ⟨hlp,hl1⟩ heta hlam.1 hcut hr.1
  have hρ : rho ∈ Ioc (0:ℝ) 1 := ⟨harith.1,hr.2⟩
  have hminF : ∀ ν ∈ scalarFloor (lam/β),
      followupEnergyFunctional n β lam rho μ ≤ followupEnergyFunctional n β lam rho ν := by
    intro ν hν
    exact div_le_div_of_nonneg_right (hmin ν hν) hb.le
  have hvalue : followupEnergyFunctional n β lam rho μ=
      followupEnergyMinimum n hnp β lam rho hb hlβ harith.1.le := by
    apply le_antisymm
    · simpa only [followupMinimizer_value] using hminF
        (followupMinimizer n hnp β lam rho hb hlβ harith.1.le)
        (followupMinimizer_mem_floor n hnp β lam rho hb hlβ harith.1.le)
    · exact followupEnergyMinimum_le hnp β lam rho hb hlβ harith.1.le μ hμ
  obtain ⟨hstrial,hν,hzero,hmid,hcost⟩ := htrial (parisiMinimizer β 0)
    (isParisiMinimizer_selected β 0) lam ⟨hlp.le,by linarith [hlam.2,h0.1]⟩
  let ν := scalarClippedTrialMeasure (lam/β) hstrial (parisiMinimizer β 0)
  have hbudget0 := foundation_trial_budget n hnp β lam (1-rho) L hb hs
    ⟨by linarith [hr.2],by linarith [harith.1]⟩ μ ν hμ hν hmin hzero hcost
  have hbudget : followupEnergyFunctional n β lam rho ν ≤
      followupEnergyMinimum n hnp β lam rho hb hlβ harith.1.le+eta := by
    have hbudget1 := hbudget0.2
    change followupEnergyFunctional n β lam rho ν-followupEnergyFunctional n β lam rho μ ≤ eta at hbudget1
    rw [hvalue] at hbudget1
    linarith
  have hmodel := hstable n hn μ lam rho eta ⟨hlp.le,hlβ⟩ hρ hμ hminF hη hbudget
  exact ⟨harith.1,harith.2.1,hmodel.2.1,hmodel.2.2.1.trans harith.2.2⟩

end QuantitativeFollowup
