module
public import QuantitativeFollowup.RootAnyMinimizerRegularization
public import QuantitativeFollowup.RootScalarTrialData
public import QuantitativeFollowup.RootPushedSegment

@[expose] public section

/-! Root localization construction for every actual minimizer, including
all floor and trial-budget quantifiers. No uniqueness claim or response
inequality is assumed. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FRSB
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000

theorem root_any_minimizer_localization_construction (beta : ℝ) (hbeta : 1 < beta) :
    ∃k C T : ℝ, 0 < k ∧ 1 ≤ C ∧ T ∈ Ioc (0 : ℝ) (1/4) ∧ k*T ≤ 2 ∧
      ∀n : ℕ, ∀hn : 0 < n, ∀μ : Paper.ParisiMeasure, ∀lam rho eta v q : ℝ,
      ∀hlam : lam ∈ Icc (0 : ℝ) beta, ∀hrho : rho ∈ Ioc (0 : ℝ) 1,
      μ ∈ scalarFloor (lam/beta) →
      (∀ν∈scalarFloor (lam/beta), followupEnergyFunctional n beta lam rho μ ≤
        followupEnergyFunctional n beta lam rho ν) →
      0 < eta → 0 < v → q ∈ Ioc (0 : ℝ) T →
      q ≤ (parisiFreeQuantile μ (lam/beta) (v/beta) : ℝ) →
      16*(lam+v) < k*q → rootConcentratingStep rho q eta ≤ (k/2)*(q/2)^2/64 →
      let ν := scalarClippedTrialMeasure (lam/beta)
        ⟨div_nonneg hlam.1 (zero_lt_one.trans hbeta).le,
          (div_le_one (zero_lt_one.trans hbeta)).mpr hlam.2⟩ (parisiMinimizer beta 0)
      followupEnergyFunctional n beta lam rho ν ≤
        followupEnergyMinimum n hn beta lam rho (zero_lt_one.trans hbeta) hlam.2 hrho.1.le+eta →
      let m := beta*(parisiFreeMeasure μ (lam/beta)).real (overlapBelow q)
      let h := rootSmoothingWidth q eta rho m
      ∃bar : Paper.ParisiMeasure, ∃P : ℝ → Paper.ParisiMeasure,
        0 ≤ m ∧ m ≤ v ∧ 0 < h ∧ h ≤ q/8 ∧
        m/h ≤ 8*m/q+m*Real.sqrt (rho*m/eta) ∧
        bar ∈ scalarFloor (lam/beta) ∧ beta*parisiCDF bar 0=lam ∧
        followupEnergyFunctional n beta lam rho bar ≤
          followupEnergyMinimum n hn beta lam rho (zero_lt_one.trans hbeta) hlam.2 hrho.1.le+eta/12 ∧
        (∀theta∈Icc (0 : ℝ) 1,
          P theta ∈ scalarFloor (lam/beta) ∧
          ∀x : ℝ, beta*parisiCDF (P theta) x=beta*parisiCDF bar x+
            theta*concentratingPushedDirection bar ν beta (q/4) (q/2)
              (rootConcentratingStep rho q eta) x) ∧
        (∀theta∈Icc (1/4 : ℝ) (3/4),
          2*q/15 ≤ vectorConcentratingDelta (n:=n) (P theta) beta (1-rho) (lam/beta)
            (by linarith [hrho.1]) (q/4) (q/2) ∧
          ENNReal.ofReal beta • (parisiCDFPrimitive (P theta)).measure.restrict (Ioo (q/4) (3*q/4)) ≤
            ENNReal.ofReal (m/h+C+k/4) • volume.restrict (Ioo (q/4) (3*q/4))) ∧
        (∀x∈Ioo (q/4) (3*q/4), k*q/16 ≤
          concentratingPushedDirection bar ν beta (q/4) (q/2) (rootConcentratingStep rho q eta) x) := by
  have hb : 0 < beta := zero_lt_one.trans hbeta
  obtain ⟨qStar,k,C,T,hqStar,hk,hC,hkC,hT,hTu,hkT,hTrial⟩ := root_scalar_trial_data beta hbeta
  refine ⟨k,C,T,hk,hC,⟨hT.1,hTu⟩,hkT,?_⟩
  intro n hn μ lam rho eta v q hlam hrho hμ hminimal heta hv hq hQuantile hLarge hRoom
  have hs : lam/beta ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hlam.1 hb.le,(div_le_one hb).mpr hlam.2⟩
  let ν := scalarClippedTrialMeasure (lam/beta) hs (parisiMinimizer beta 0)
  dsimp only
  intro hBudget
  let m := beta*(parisiFreeMeasure μ (lam/beta)).real (overlapBelow q)
  let h := rootSmoothingWidth q eta rho m
  have hqu : q ∈ Ioc (0 : ℝ) (1/4) := ⟨hq.1,hq.2.trans hTu⟩
  obtain ⟨hm,hmv,hh,hhu,hmbudget,hInverse,bar,hbar,hRoot,hNear,hProfile,hDensity⟩ :=
    root_regularized_any_minimizer_data n hn μ beta lam rho q eta v hb hlam hrho
      hμ hminimal hqu heta hv hQuantile
  have hLargeTrial : 4*lam ≤ k*q := by nlinarith [hlam.1,hv]
  obtain ⟨hν,hνProfile,hLower,hUpper⟩ := hTrial lam q hlam hq hLargeTrial
  have hLargeMass : 16*(lam+m) < k*q := by linarith
  obtain ⟨P,hP,hContact,hSign⟩ := root_pushed_segment n hn bar ν beta lam rho q eta k C m h
    hb hlam hrho.1 hqu heta hk (zero_le_one.trans hC) hm hh hbar hν hNear hBudget
    hProfile hνProfile hLargeMass hLower hUpper hDensity hRoom
  exact ⟨bar,P,hm,hmv,hh,hhu,hInverse,hbar,hRoot,hNear,hP,hContact,hSign⟩

end QuantitativeFollowup
