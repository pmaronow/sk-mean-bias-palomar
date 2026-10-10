module
public import QuantitativeFollowup.RootAnyMinimizerConstruction
public import QuantitativeFollowup.RootPushedMidpointBalance
public import QuantitativeFollowup.RootQuantileArithmetic
public import QuantitativeFollowup.RootZeroBudget

@[expose] public section

/-! Actual root quantile localization, uniformly over every constrained
minimizer. The positive-budget branch uses the proved midpoint response;
the zero-budget endpoint follows by a genuine budget limit. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FRSB
namespace QuantitativeFollowup
set_option maxHeartbeats 3000000

theorem root_quantile_localization (beta : ℝ) (hbeta : 1 < beta) :
    ∃K : ℝ, 0 < K ∧
      ∀n : ℕ, ∀hn : 0 < n, ∀μ : Paper.ParisiMeasure, ∀lam rho eta v : ℝ,
      ∀hlam : lam ∈ Icc (0 : ℝ) beta, ∀hrho : rho ∈ Ioc (0 : ℝ) 1,
      μ ∈ scalarFloor (lam/beta) →
      (∀ν∈scalarFloor (lam/beta), followupEnergyFunctional n beta lam rho μ ≤
        followupEnergyFunctional n beta lam rho ν) →
      0 ≤ eta → 0 < v →
      let ν := scalarClippedTrialMeasure (lam/beta)
        ⟨div_nonneg hlam.1 (zero_lt_one.trans hbeta).le,
          (div_le_one (zero_lt_one.trans hbeta)).mpr hlam.2⟩ (parisiMinimizer beta 0)
      followupEnergyFunctional n beta lam rho ν ≤
        followupEnergyMinimum n hn beta lam rho (zero_lt_one.trans hbeta) hlam.2 hrho.1.le+eta →
      (parisiFreeQuantile μ (lam/beta) (v/beta) : ℝ) ≤
        K*(lam+v+min 1 ((eta/rho)^((1 : ℝ)/6))) := by
  have hb : 0 < beta := zero_lt_one.trans hbeta
  obtain ⟨k,C,T,hk,hC,hT,hkT,hConstruct⟩ :=
    root_any_minimizer_localization_construction beta hbeta
  let K := rootQuantileCoefficient beta k C T
  have hK8 : 8 ≤ K := rootQuantileCoefficient_ge_eight beta k C T hk hT.1 hkT
  have hK : 0 < K := by linarith
  refine ⟨K,hK,?_⟩
  intro n hn μ lam rho eta v hlam hrho hμ hminimal heta hv
  dsimp only
  intro hBudget
  let Q : ℝ := parisiFreeQuantile μ (lam/beta) (v/beta)
  have hQ : Q∈Icc (0 : ℝ) 1 := (parisiFreeQuantile μ (lam/beta) (v/beta)).property
  have hPositive : ∀e : ℝ, 0 < e →
      followupEnergyFunctional n beta lam rho
        (scalarClippedTrialMeasure (lam/beta)
          ⟨div_nonneg hlam.1 hb.le,(div_le_one hb).mpr hlam.2⟩ (parisiMinimizer beta 0)) ≤
        followupEnergyMinimum n hn beta lam rho hb hlam.2 hrho.1.le+e →
      Q ≤ K*(lam+v+min 1 ((e/rho)^((1 : ℝ)/6))) := by
    intro e he hBe
    let q := min Q T
    let m := beta*(parisiFreeMeasure μ (lam/beta)).real (overlapBelow q)
    have hm : 0 ≤ m := mul_nonneg hb.le ENNReal.toReal_nonneg
    have hmv : m ≤ v := parisiFreeMeasure_energy_below_quantile_le
      μ beta lam v q hb hv (min_le_left Q T)
    apply root_quantile_arithmetic Q beta k C T lam v e rho m hQ hb hk
      (zero_le_one.trans hC) hT hkT hlam.1 hv.le he hrho.1 hm hmv
    intro hLarge hRoom
    have hq0 : 0 < q := by
      have hh : 0 ≤ lam+v := add_nonneg hlam.1 hv.le
      have hp : 0 < k*q := (mul_nonneg (by norm_num : (0 : ℝ)≤16) hh).trans_lt hLarge
      exact pos_of_mul_pos_right hp hk.le
    have hq : q∈Ioc (0 : ℝ) T := ⟨hq0,min_le_right Q T⟩
    obtain ⟨bar,P,hm',hmv',hh,hhu,hInverse,hbar,hRoot,hNear,hP,hContact,hSign⟩ :=
      hConstruct n hn μ lam rho e v q hlam hrho hμ hminimal he hv hq
        (min_le_left Q T) hLarge hRoom hBe
    let d := m/rootSmoothingWidth q e rho m+C+k/4
    have hd : 0 < d := by
      have hmh : 0 ≤ m/rootSmoothingWidth q e rho m := div_nonneg hm hh.le
      dsimp only [d]
      linarith
    have hBalance := root_pushed_midpoint_balance hn P bar
      (scalarClippedTrialMeasure (lam/beta)
        ⟨div_nonneg hlam.1 hb.le,(div_le_one hb).mpr hlam.2⟩ (parisiMinimizer beta 0))
      beta lam rho q e k d hb hlam hrho.1 ⟨hq0,hq.2.trans hT.2⟩ he.le hk hd
      (fun theta ht=>(hP theta ht).1) (fun theta ht=>(hP theta ht).2)
      hContact hSign hNear hBe
    convert hBalance using 1
    dsimp only [rootBalanceConstant,d,q,m]
    ring
  by_cases he : 0 < eta
  · exact hPositive eta he hBudget
  · have he0 : eta=0 := le_antisymm (le_of_not_gt he) heta
    subst eta
    have hz : Q ≤ K*(lam+v) := root_zero_budget_limit Q K lam v rho hK hrho.1 (by
      intro e he
      apply hPositive e he
      linarith only [hBudget,he])
    simpa only [zero_div,Real.zero_rpow (by norm_num : (1 : ℝ)/6≠0),
      min_eq_right zero_le_one,add_zero] using hz

end QuantitativeFollowup
