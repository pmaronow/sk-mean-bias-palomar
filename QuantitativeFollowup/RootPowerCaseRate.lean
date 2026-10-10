module
public import QuantitativeFollowup.RootDensityRate

@[expose] public section

/-! The final sixth/fourth-power branch of the root rate proof, with the
paper's constants. The actual response balance is an explicit input to
this deterministic endpoint, not a premise hidden in a model theorem. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1500000

def rootBalanceConstant (k : ℝ) : ℝ := 294912/k^2

def rootFourthConstant (k : ℝ) : ℝ := 15*rootBalanceConstant k/2

def rootPowerCaseConstant (beta k C : ℝ) : ℝ :=
  max ((3840*beta*rootBalanceConstant k/7)^((1 : ℝ)/6))
    (max ((2*rootFourthConstant k*(C+5*k/4))^((1 : ℝ)/4))
      ((2*rootFourthConstant k)^((1 : ℝ)/4)))

theorem rootPowerCaseConstant_pos (beta k C : ℝ) (hbeta : 0 < beta) (hk : 0 < k) :
    0 < rootPowerCaseConstant beta k C := by
  apply lt_of_lt_of_le _ (le_max_left _ _)
  apply Real.rpow_pos_of_pos
  unfold rootBalanceConstant
  positivity

theorem root_power_case_rate (q eta rho m v lam beta k C : ℝ)
    (hq : 0 < q) (heta : 0 < eta) (hrho : 0 < rho) (hetrho : eta ≤ rho)
    (hm : 0 ≤ m) (hmv : m ≤ v) (hlam : 0 ≤ lam)
    (hbeta : 0 < beta) (hk : 0 < k) (hC : 0 ≤ C)
    (hlarge : 16*(lam+v) ≤ k*q)
    (hbalance : min (7*q^3/(3840*beta))
        (2*q/(15*(m/rootSmoothingWidth q eta rho m+C+k/4))) ≤
      rootBalanceConstant k*(eta/rho)/q^3) :
    q ≤ rootPowerCaseConstant beta k C*((eta/rho)^((1 : ℝ)/6)+lam+v) := by
  have hWidth := rootSmoothingWidth_pos_le q eta rho m hq heta hrho hm
  have hDensity : 0 < m/rootSmoothingWidth q eta rho m+C+k/4 := by
    positivity [hWidth.1]
  have hB : 0 ≤ rootFourthConstant k := by unfold rootFourthConstant rootBalanceConstant; positivity
  have hCoef : 0 ≤ 3840*beta*rootBalanceConstant k/7 := by
    unfold rootBalanceConstant
    positivity
  have hSmall : 8*m/q ≤ k := by
    apply (div_le_iff₀ hq).mpr
    nlinarith
  have hδ : eta/rho ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg heta.le hrho.le,(div_le_one hrho).mpr hetrho⟩
  have hSum : 0 ≤ (eta/rho)^((1 : ℝ)/6)+lam+v := by
    positivity [hm.trans hmv]
  rcases root_balance_power_cases q beta (rootBalanceConstant k) (eta/rho)
    (m/rootSmoothingWidth q eta rho m+C+k/4) hq hbeta hDensity hbalance with hFirst|hSecond
  · have hr := root_sixth_rate q (3840*beta*rootBalanceConstant k/7) (eta/rho) hq.le
      hCoef hδ.1 hFirst
    calc
      q ≤ (3840*beta*rootBalanceConstant k/7)^((1 : ℝ)/6)*(eta/rho)^((1 : ℝ)/6) := hr
      _ ≤ (3840*beta*rootBalanceConstant k/7)^((1 : ℝ)/6)*((eta/rho)^((1 : ℝ)/6)+lam+v) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hm.trans hmv]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hSum
  · have hr := root_density_case_rate q eta rho m k C (rootFourthConstant k) hq.le heta hrho
      hetrho hm hk.le hC hB hSmall hSecond
    calc
      q ≤ max ((2*rootFourthConstant k*(C+5*k/4))^((1 : ℝ)/4))
          ((2*rootFourthConstant k)^((1 : ℝ)/4))*((eta/rho)^((1 : ℝ)/6)+m) := hr
      _ ≤ max ((2*rootFourthConstant k*(C+5*k/4))^((1 : ℝ)/4))
          ((2*rootFourthConstant k)^((1 : ℝ)/4))*((eta/rho)^((1 : ℝ)/6)+lam+v) := by
        apply mul_le_mul_of_nonneg_left _ (le_max_of_le_left (by positivity))
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hSum

end QuantitativeFollowup
