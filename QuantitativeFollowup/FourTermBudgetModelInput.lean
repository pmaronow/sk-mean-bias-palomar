module
public import QuantitativeFollowup.FourTermBudgetCutoffPowers
public import QuantitativeFollowup.FourTermBudgetTrial
public import QuantitativeFollowup.StableIntervalCutoff
public import QuantitativePaper.ShortVarianceMeanUniform

@[expose] public section

/-! Actual native comparison input from the proved small-interval model.
The sole remaining supporting premise is the separate stable-interval
integral, whose full actual-model theorem is constructed independently. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000

 theorem fourTermBudget_actual_input (β : ℝ) (hβ : 1<β) :
    ∃Cs : ℝ,0<Cs ∧ ∀n : ℕ,∀hn : 2 ≤ n,∀lam L Cst Ct : ℝ,
      ∀hlam : lam∈Ioc (0:ℝ) (min 1 (β/4)),1 ≤ L  →  1 ≤ Cst  →  0 ≤ Ct  → 
      let eta:=energyComparisonError n β lam+L*lam^5
      let rho0:=stableIntervalCutoff Cst eta
      (∀rho : ℝ,∀hrho : rho∈Ioc (0:ℝ) 1,
        smallIntervalTrialGap n (by omega) β lam rho (zero_lt_one.trans hβ)
          ⟨hlam.1.le,by linarith [hlam.2.trans (min_le_right 1 (β/4))]⟩ hrho.1.le ≤ eta)  → 
      (rho0<1  →  (∫rho in rho0..(1:ℝ),smallIntervalDefect n β lam rho) ≤ 
        Ct*(Real.log (2+(n:ℝ)))^2/((n:ℝ)*lam^(12/7:ℝ)))  → 
      energyComparisonError n β lam ≤ 
        fourTermBudgetInputConstant Cs Ct (12*Cst)*(Real.log (2+(n:ℝ)))^3/((n:ℝ)*lam^(12/7:ℝ))+
        (fourTermBudgetInputConstant Cs Ct (12*Cst)*(n:ℝ)^(-(2/3:ℝ)))*eta^(1/21:ℝ)+
        (fourTermBudgetInputConstant Cs Ct (12*Cst)*(n:ℝ)^(-(2/3:ℝ))*lam^(-(1/3:ℝ)))*eta^(1/7:ℝ) := by
  obtain ⟨Cs,hCs,hSmall⟩:=small_interval_integrated_model β hβ
  refine ⟨Cs,hCs,?_⟩
  intro n hn lam L Cst Ct hlam hL hCst hCt
  dsimp only
  intro hTrial hStable
  have hn0 : 0<n:=by omega
  have hN : (2:ℝ) ≤ n:=by exact_mod_cast hn
  have hβp : 0<β:=zero_lt_one.trans hβ
  have hlamβ : lam ≤ β:=by linarith [hlam.2.trans (min_le_right 1 (β/4))]
  have hlam1 : lam∈Ioc (0:ℝ) 1:=⟨hlam.1,hlam.2.trans (min_le_left 1 (β/4))⟩
  have hs : lam/β∈Ioo (0:ℝ) 1:=⟨div_pos hlam.1 hβp,(div_lt_one hβp).mpr
    (by linarith [hlam.2.trans (min_le_right 1 (β/4))])⟩
  let e:=energyComparisonError n β lam
  let eta:=e+L*lam^5
  let rho0:=stableIntervalCutoff Cst eta
  have he : 0 ≤ e:=energyComparisonError_nonneg n hn0 β hβp lam hs
  have hetaLower : lam^5 ≤ eta:=by
    have hh:=mul_le_mul_of_nonneg_right hL (pow_nonneg hlam.1.le 5)
    dsimp only [eta]
    linarith
  have heta : 0<eta:=(pow_pos hlam.1 5).trans_le hetaLower
  have hcut:=stableIntervalCutoff_bounds Cst eta lam hCst hlam.1 hetaLower
  have hrho : rho0∈Ioc (0:ℝ) 1:=⟨hcut.1,min_le_left _ _⟩
  have hwhole:=fourTermBudget_native_envelope n hn0 β lam hβp hs
  have hsb:=hSmall n hn lam eta rho0 hlam hrho heta.le (fun rho hr=>
    hTrial rho ⟨hr.1,hr.2.trans hrho.2⟩)
  apply fourTermBudget_input_from_intervals (n:ℝ) lam e eta Cs Ct (12*Cst) rho0
    hN hlam1 he heta hCs.le hCt (by positivity) hrho hcut.2.2
    (smallIntervalDefect n β lam) hwhole.2 hwhole.1
  · simpa only [smallIntervalIntegratedBudget,one_div] using hsb.2
  · exact hStable

end QuantitativeFollowup
