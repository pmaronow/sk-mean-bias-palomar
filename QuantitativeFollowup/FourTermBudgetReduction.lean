module
public import QuantitativeFollowup.FourTermBudgetModelInput

@[expose] public section

/-! Native comparison reduction with its remaining global stable-interval
hypothesis explicit. The actual clipped trial constants are chosen here;
no identification with another theorem's chosen L is assumed. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 2600000

def FourTermStableIntegralHypothesis (β : ℝ) (hβ : 1<β) (lambdaSt Cst Ct : ℝ) : Prop :=
  ∀n : ℕ,∀hn : 2 ≤ n,∀lam eta : ℝ,∀hlam : lam∈Icc ((n:ℝ)⁻¹) lambdaSt,
    ∀hlamβ : lam∈Icc (0:ℝ) β,lam^5 ≤ eta  → 
    (∀rho : ℝ,∀hrho : rho∈Ioc (0:ℝ) 1,
      smallIntervalTrialGap n (by omega) β lam rho (zero_lt_one.trans hβ) hlamβ hrho.1.le ≤ eta)  → 
    stableIntervalCutoff Cst eta<1  → 
    (∫rho in (stableIntervalCutoff Cst eta)..(1:ℝ),smallIntervalDefect n β lam rho) ≤ 
      Ct*(Real.log (2+(n:ℝ)))^2/((n:ℝ)*lam^(12/7:ℝ))

 theorem four_term_budget_of_stable_integral (β : ℝ) (hβ : 1<β)
    (lambdaSt Cst Ct : ℝ) (hSt : lambdaSt∈Ioc (0:ℝ) 1) (hStβ : lambdaSt ≤ β/4)
    (hCst : 1 ≤ Cst) (hCt : 0 ≤ Ct)
    (hStable : FourTermStableIntegralHypothesis β hβ lambdaSt Cst Ct) :
    ∃C L lambda0 : ℝ,0<C ∧ 1 ≤ L ∧ lambda0∈Ioc (0:ℝ) 1 ∧ lambda0 ≤ β/4 ∧
      ∀n : ℕ,∀hn : 2 ≤ n,∀lam∈Icc ((n:ℝ)⁻¹) lambda0,
      0 ≤ energyComparisonError n β lam ∧
      energyComparisonError n β lam ≤ C*fourTermBudgetRate (n:ℝ) lam := by
  obtain ⟨L,lambdaTrial,hL,hTrial0,hTrialβ,hTrial⟩:=fourTermBudget_actual_trial β hβ
  obtain ⟨Cs,hCs,hActual⟩:=fourTermBudget_actual_input β hβ
  let lambda0:=min lambdaTrial lambdaSt
  let Cinput:=fourTermBudgetInputConstant Cs Ct (12*Cst)
  let C:=fourTermBudgetAbsorptionConstant Cinput L
  have hCinput : 0<Cinput:=fourTermBudgetInputConstant_pos Cs Ct (12*Cst) hCs.le hCt (by positivity)
  have hCp : 0<C:=fourTermBudgetAbsorptionConstant_pos Cinput L hCinput.le (zero_le_one.trans hL)
  have h0 : lambda0∈Ioc (0:ℝ) 1:=⟨lt_min hTrial0.1 hSt.1,(min_le_left _ _).trans hTrial0.2⟩
  have h0β : lambda0 ≤ β/4:=(min_le_left _ _).trans hTrialβ
  refine ⟨C,L,lambda0,hCp,hL,h0,h0β,?_⟩
  intro n hn lam hlam
  have hn0 : 0<n:=by omega
  have hN : (2:ℝ) ≤ n:=by exact_mod_cast hn
  have hNp : 0<(n:ℝ):=Nat.cast_pos.mpr hn0
  have hβp : 0<β:=zero_lt_one.trans hβ
  have hlp : 0<lam:=(inv_pos.mpr hNp).trans_le hlam.1
  have hlTrial : lam∈Ioc (0:ℝ) lambdaTrial:=⟨hlp,hlam.2.trans (min_le_left _ _)⟩
  have hlSt : lam∈Icc ((n:ℝ)⁻¹) lambdaSt:=⟨hlam.1,hlam.2.trans (min_le_right _ _)⟩
  have hlβ : lam∈Icc (0:ℝ) β:=⟨hlp.le,by linarith [hlam.2.trans h0β]⟩
  have hlSmall : lam∈Ioc (0:ℝ) (min 1 (β/4)):=⟨hlp,le_min (hlam.2.trans h0.2) (hlam.2.trans h0β)⟩
  have hlUnit : lam∈Ioc (0:ℝ) 1:=⟨hlp,hlam.2.trans h0.2⟩
  have hs : lam/β∈Ioo (0:ℝ) 1:=⟨div_pos hlp hβp,(div_lt_one hβp).mpr (by linarith [hlam.2.trans h0β])⟩
  let e:=energyComparisonError n β lam
  let eta:=e+L*lam^5
  have he : 0 ≤ e:=energyComparisonError_nonneg n hn0 β hβp lam hs
  have hEta : lam^5 ≤ eta:=by
    have hh:=mul_le_mul_of_nonneg_right hL (pow_nonneg hlp.le 5)
    dsimp only [eta]
    linarith
  have hBudget : ∀rho : ℝ,∀hrho : rho∈Ioc (0:ℝ) 1,
      smallIntervalTrialGap n hn0 β lam rho hβp hlβ hrho.1.le ≤ eta:=
    fun rho hrho=>hTrial n hn0 lam hlTrial rho hrho
  have htail:=hStable n hn lam eta hlSt hlβ hEta hBudget
  have hinput:=hActual n hn lam L Cst Ct hlSmall hL hCst hCt hBudget htail
  refine ⟨he,?_⟩
  exact fourTermBudget_absorption (n:ℝ) lam e Cinput L (by linarith) hlUnit he
    hCinput.le (zero_le_one.trans hL) hinput

end QuantitativeFollowup
