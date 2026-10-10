module
public import QuantitativeFollowup.StableIntervalModel
public import QuantitativeFollowup.SmallIntervalModel

@[expose] public section

/-! Actual stability for every native minimizing profile under an arbitrary
honest trial budget eta. The cutoff constants do not depend on a selected
trial theorem's particular L. -/
noncomputable section
open Set MeasureTheory Paper FRSB QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000

theorem stable_interval_budget_actual_minimizers (β : ℝ) (hβ : 1<β) :
    ∃C : ℝ,1 ≤ C ∧ ∀n : ℕ,∀hn : 2 ≤ n,∀lam eta : ℝ,
      ∀hlam : lam∈Icc ((n:ℝ)⁻¹) (min 1 (β/4)),lam^5 ≤ eta →
      (∀rho : ℝ,∀hrho : rho∈Ioc (0:ℝ) 1,
        smallIntervalTrialGap n (by omega) β lam rho (zero_lt_one.trans hβ)
          ⟨(inv_pos.mpr (Nat.cast_pos.mpr (show 0<n by omega))).le.trans hlam.1,
            by linarith [hlam.2.trans (min_le_right 1 (β/4))]⟩ hrho.1.le ≤ eta) →
      stableIntervalCutoff C eta<1 → ∀rho∈Icc (stableIntervalCutoff C eta) 1,
      ∀μ : Paper.ParisiMeasure,μ∈scalarFloor (lam/β) →
      (∀ν∈scalarFloor (lam/β),vectorMeasureFunctional n μ β (1-rho) (lam/β) ≤
        vectorMeasureFunctional n ν β (1-rho) (lam/β)) →
      0<rho ∧ (n:ℝ)⁻¹ ≤ rho ∧
        scalarOperatorStabilityError β μ (followupScalarCoefficient n β rho) ≤ rho/4 := by
  obtain ⟨C,hC,hStable⟩:=scalar_minimizer_stability β hβ
  have hβp : 0<β:=zero_lt_one.trans hβ
  refine ⟨C,hC,?_⟩
  intro n hn lam eta hlam heta hTrial hcut rho hr μ hμ hmin
  have hn0 : 0<n:=by omega
  have hN : 0<(n:ℝ):=Nat.cast_pos.mpr hn0
  have hlp : 0<lam:=(inv_pos.mpr hN).trans_le hlam.1
  have hlunit : lam∈Ioc (0:ℝ) 1:=⟨hlp,hlam.2.trans (min_le_left 1 (β/4))⟩
  have hlβ : lam∈Icc (0:ℝ) β:=⟨hlp.le,by linarith [hlam.2.trans (min_le_right 1 (β/4))]⟩
  have harith:=stableIntervalCutoff_stability C eta lam ((n:ℝ)⁻¹) rho hC hlunit heta hlam.1 hcut hr.1
  have hrho : rho∈Ioc (0:ℝ) 1:=⟨harith.1,hr.2⟩
  have hminF : ∀ν∈scalarFloor (lam/β),followupEnergyFunctional n β lam rho μ ≤
      followupEnergyFunctional n β lam rho ν := fun ν hν=>
    div_le_div_of_nonneg_right (hmin ν hν) hβp.le
  have hvalue : followupEnergyFunctional n β lam rho μ=
      followupEnergyMinimum n hn0 β lam rho hβp hlβ.2 hrho.1.le := by
    apply le_antisymm
    · simpa only [followupMinimizer_value] using hminF
        (followupMinimizer n hn0 β lam rho hβp hlβ.2 hrho.1.le)
        (followupMinimizer_mem_floor n hn0 β lam rho hβp hlβ.2 hrho.1.le)
    · exact followupEnergyMinimum_le hn0 β lam rho hβp hlβ.2 hrho.1.le μ hμ
  have hbudget : followupEnergyFunctional n β lam rho
      (scalarClippedTrialMeasure (lam/β)
        ⟨div_nonneg hlβ.1 hβp.le,(div_le_one hβp).mpr hlβ.2⟩ (parisiMinimizer β 0)) ≤
      followupEnergyMinimum n hn0 β lam rho hβp hlβ.2 hrho.1.le+eta := by
    have hh := hTrial rho hrho
    change smallIntervalTrialGap n hn0 β lam rho hβp hlβ hrho.1.le ≤ eta at hh
    unfold smallIntervalTrialGap at hh
    linarith
  have hmodel:=hStable n hn μ lam rho eta hlβ hrho hμ hminF
    ((pow_nonneg hlp.le 5).trans heta) hbudget
  exact ⟨harith.1,harith.2.1,hmodel.2.2.1.trans harith.2.2⟩

end QuantitativeFollowup
