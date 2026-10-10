module
public import QuantitativeFollowup.RootQuantileLocalization

@[expose] public section

/-! Literal probability-normalized root quantile bound. This is a
normalization of the actual universal minimizing-profile endpoint,
including the zero trial budget. -/
noncomputable section
open Set Paper QuantitativePaper FRSB
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem probability_root_quantile_localization (beta : ℝ) (hbeta : 1<beta) :
    ∃K : ℝ,1≤K ∧
      ∀n : ℕ,∀hn : 0<n,∀μ : Paper.ParisiMeasure,∀lam rho eta v : ℝ,
      ∀hlam : lam∈Icc (0 : ℝ) beta,∀hrho : rho∈Ioc (0 : ℝ) 1,
      μ∈scalarFloor (lam/beta)→
      (∀ν∈scalarFloor (lam/beta),followupEnergyFunctional n beta lam rho μ≤
        followupEnergyFunctional n beta lam rho ν)→
      0≤eta→0<v→
      let ν := scalarClippedTrialMeasure (lam/beta)
        ⟨div_nonneg hlam.1 (zero_lt_one.trans hbeta).le,
          (div_le_one (zero_lt_one.trans hbeta)).mpr hlam.2⟩ (parisiMinimizer beta 0)
      followupEnergyFunctional n beta lam rho ν≤
        followupEnergyMinimum n hn beta lam rho (zero_lt_one.trans hbeta) hlam.2 hrho.1.le+eta→
      (parisiFreeQuantile μ (lam/beta) v : ℝ)≤
        K*(lam/beta+v+min 1 ((eta/rho)^((1 : ℝ)/6))) := by
  have hb : 0<beta := zero_lt_one.trans hbeta
  obtain ⟨C,hC,hRoot⟩ := root_quantile_localization beta hbeta
  let K := max 1 (beta*C)
  refine ⟨K,le_max_left _ _,?_⟩
  intro n hn μ lam rho eta v hlam hrho hμ hminimal heta hv
  dsimp only
  intro hBudget
  have hh := hRoot n hn μ lam rho eta (beta*v) hlam hrho hμ hminimal heta (mul_pos hb hv) hBudget
  have hquot : beta*v/beta=v := by field_simp
  rw [hquot] at hh
  have homega : 0 ≤ min 1 ((eta/rho)^((1 : ℝ)/6)) :=
    le_min zero_le_one (Real.rpow_nonneg (div_nonneg heta hrho.1.le) _)
  have hsum : 0≤lam/beta+v+min 1 ((eta/rho)^((1 : ℝ)/6)) :=
    add_nonneg (add_nonneg (div_nonneg hlam.1 hb.le) hv.le) homega
  have hscaled : C*(lam+beta*v+min 1 ((eta/rho)^((1 : ℝ)/6)))≤
      (beta*C)*(lam/beta+v+min 1 ((eta/rho)^((1 : ℝ)/6))) := by
    have hroot : beta*(lam/beta)=lam := by field_simp
    nlinarith only [hroot,mul_nonneg (sub_nonneg.mpr hbeta.le) homega,hC]
  exact hh.trans (hscaled.trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 (beta*C)) hsum))

end QuantitativeFollowup
