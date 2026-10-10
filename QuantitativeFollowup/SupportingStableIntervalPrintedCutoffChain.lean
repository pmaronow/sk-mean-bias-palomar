module
public import QuantitativeFollowup.StableIntervalModel

@[expose] public section

/-! The literal cutoff chains and numerical response-operator error at the
actual minimizing model. All trial, localization and operator inputs come
from the already proved model, rather than a presumed response bound. -/
noncomputable section
open Set MeasureTheory Paper FRSB QuantitativePaper FourPapersCommon
open scoped Topology
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Both chains printed before the scalar operator estimate. -/
theorem stableIntervalCutoff_printed_lower_chains (C eta lam invN rho : ℝ)
    (hC : 1 ≤ C) (hlam : lam∈Ioc (0:ℝ) 1) (heta : lam^5 ≤ eta)
    (hN : invN ≤ lam) (hN0 : 0 ≤ invN)
    (hcut : stableIntervalCutoff C eta < 1)
    (hrho : stableIntervalCutoff C eta ≤ rho) :
    12*C*eta^((1:ℝ)/7) ≤ rho ∧
    12*C*lam^((5:ℝ)/7) ≤ 12*C*eta^((1:ℝ)/7) ∧
    12*C*lam^2 ≤ 12*C*lam^((5:ℝ)/7) ∧
    12*C*lam ≤ 12*C*lam^((5:ℝ)/7) ∧
    12*C*invN ≤ 12*C*lam ∧ invN ≤ 12*C*invN := by
  have hetap : 0 < eta := (pow_pos hlam.1 5).trans_le heta
  have hK : 0 ≤ 12*C := by linarith
  have hsmall : 12*C*eta^((1:ℝ)/7) < 1 := by
    by_contra hn
    have hh : 1 ≤ 12*C*eta^((1:ℝ)/7) := le_of_not_gt hn
    simp only [stableIntervalCutoff,min_eq_left hh] at hcut
    exact lt_irrefl 1 hcut
  have hbase : 12*C*eta^((1:ℝ)/7) ≤ rho := by
    simpa only [stableIntervalCutoff,min_eq_right hsmall.le] using hrho
  have hp := Real.rpow_le_rpow (pow_nonneg hlam.1.le 5) heta
    (by norm_num : 0 ≤ (1:ℝ)/7)
  have he : (lam^5)^((1:ℝ)/7)=lam^((5:ℝ)/7) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hlam.1.le]
    congr 1
    norm_num
  rw [he] at hp
  have hl1 : lam ≤ lam^((5:ℝ)/7) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hlam.1 hlam.2
        (by norm_num : (5:ℝ)/7 ≤ 1)
  have hl2 : lam^2 ≤ lam^((5:ℝ)/7) := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_ge hlam.1 hlam.2
        (by norm_num : (5:ℝ)/7 ≤ 2)
  exact ⟨hbase,mul_le_mul_of_nonneg_left hp hK,
    mul_le_mul_of_nonneg_left hl2 hK,mul_le_mul_of_nonneg_left hl1 hK,
    mul_le_mul_of_nonneg_left hN hK,
    le_mul_of_one_le_left hN0 (by linarith)⟩

/-- The literal epsilon is nonnegative on its genuine domain. -/
theorem stableInterval_printed_epsilon_nonneg (C eta lam invN rho : ℝ)
    (hC : 0 ≤ C) (heta : 0 ≤ eta) (hN : 0 ≤ invN) (hrho : 0 ≤ rho) :
    0 ≤ C*(rho^((-3:ℝ)/4)*eta^((1:ℝ)/4)+lam^2+invN) :=
  mul_nonneg hC (add_nonneg
    (add_nonneg (mul_nonneg (Real.rpow_nonneg hrho _) (Real.rpow_nonneg heta _))
      (sq_nonneg lam)) hN)

/-- Literal displayed epsilon bounds the actual response quadratic form
for every actual constrained minimizer, with the trial budget discharged. -/
theorem stable_interval_actual_minimizers_printed_operator (β : ℝ) (hβ : 1 < β) :
    ∃ L lambda0 C : ℝ, 1 ≤ L ∧ lambda0∈Ioc (0:ℝ) 1 ∧
      lambda0 ≤ β/4 ∧ 1 ≤ C ∧
      ∀ n : ℕ, ∀ hn : 2 ≤ n, ∀ lam : ℝ,
      lam∈Icc ((n:ℝ)⁻¹) lambda0 →
      let eta := stableIntervalTrialBudget n β lam L
      stableIntervalCutoff C eta < 1 →
      ∀ rho∈Icc (stableIntervalCutoff C eta) 1,
      ∀ μ : Paper.ParisiMeasure, ∀ hμ : μ∈scalarFloor (lam/β),
      (∀ ν∈scalarFloor (lam/β),
        vectorMeasureFunctional n μ β (1-rho) (lam/β) ≤
          vectorMeasureFunctional n ν β (1-rho) (lam/β)) →
      let epsilon := C*(rho^((-3:ℝ)/4)*eta^((1:ℝ)/4)+lam^2+(n:ℝ)⁻¹)
      0 < rho ∧ (n:ℝ)⁻¹ ≤ rho ∧ 0 ≤ epsilon ∧ epsilon ≤ rho/4 ∧
      ∀ hs : lam/β∈Icc (0:ℝ) 1,
      ∀ hd : 0 < followupScalarCoefficient n β rho,
      ∀ f : endpointFixedL2 (parisiFreeMeasure μ (lam/β)),
        inner ℝ f (scalarResponseL2Operator
          (Real.sqrt (followupScalarCoefficient n β rho))
          (Real.sqrt_pos.mpr hd).ne' μ (lam/β) hs hμ f) ≤ (1+epsilon)*‖f‖^2 := by
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
  have hs : lam/β∈Ioo (0:ℝ) 1 := by
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
  dsimp only
  intro hcut rho hr μ hμ hmin
  have harith := stableIntervalCutoff_stability C eta lam ((n:ℝ)⁻¹) rho
    hC ⟨hlp,hl1⟩ heta hlam.1 hcut hr.1
  have hρ : rho∈Ioc (0:ℝ) 1 := ⟨harith.1,hr.2⟩
  have hminF : ∀ ν∈scalarFloor (lam/β),
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
  have hninv : 0 ≤ (n:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  refine ⟨harith.1,harith.2.1,
    stableInterval_printed_epsilon_nonneg C eta lam ((n:ℝ)⁻¹) rho
      (zero_le_one.trans hC) hη hninv harith.1.le,harith.2.2,?_⟩
  intro hs' hd f
  exact (hmodel.2.2.2 hμ f).trans
    (mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) hmodel.2.2.1) (sq_nonneg ‖f‖))

end QuantitativeFollowup
