module
public import QuantitativeFollowup.FollowupMinimizer
public import QuantitativeFollowup.FreeQuantileBelowMass
public import QuantitativeFollowup.RootSmoothingWidth
public import QuantitativeFollowup.PartialLocalizationDensity

@[expose] public section

/-! Actual root-localization Step 1: the chosen compact minimizer is
partially regularized using its genuine mass strictly below a free
quantile. No density or regularization-cost conclusion is supplied. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem root_regularized_minimizer_data (n : ℕ) (hn : 0 < n)
    (beta lam rho q eta v : ℝ) (hbeta : 0 < beta)
    (hlam : lam ∈ Icc (0 : ℝ) beta) (hrho : rho ∈ Ioc (0 : ℝ) 1)
    (hq : q ∈ Ioc (0 : ℝ) (1/4)) (heta : 0 < eta) (hv : 0 < v)
    (hquantile : q ≤ (parisiFreeQuantile
      (followupMinimizer n hn beta lam rho hbeta hlam.2 hrho.1.le)
        (lam/beta) (v/beta) : ℝ)) :
    let μ := followupMinimizer n hn beta lam rho hbeta hlam.2 hrho.1.le
    let m := beta*(parisiFreeMeasure μ (lam/beta)).real (overlapBelow q)
    let h := rootSmoothingWidth q eta rho m
    0 ≤ m ∧ m ≤ v ∧ 0 < h ∧ h ≤ q/8 ∧ rho*m*h^2 ≤ eta ∧
    m/h ≤ 8*m/q+m*Real.sqrt (rho*m/eta) ∧
    ∃bar : Paper.ParisiMeasure,
      bar ∈ scalarFloor (lam/beta) ∧ beta*parisiCDF bar 0=lam ∧
      followupEnergyFunctional n beta lam rho bar ≤
        followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.1.le+eta/12 ∧
      (∀x∈Ico (0 : ℝ) q, beta*parisiCDF bar x ≤ lam+m) ∧
      ENNReal.ofReal beta • (parisiCDFPrimitive bar).measure.restrict (Ioo (q/4) (3*q/4)) ≤
        ENNReal.ofReal (m/h) • volume.restrict (Ioo (q/4) (3*q/4)) := by
  let μ := followupMinimizer n hn beta lam rho hbeta hlam.2 hrho.1.le
  let m := beta*(parisiFreeMeasure μ (lam/beta)).real (overlapBelow q)
  let h := rootSmoothingWidth q eta rho m
  have hm : 0 ≤ m := mul_nonneg hbeta.le ENNReal.toReal_nonneg
  have hmv : m ≤ v := parisiFreeMeasure_energy_below_quantile_le μ beta lam v q hbeta hv hquantile
  have hh := rootSmoothingWidth_pos_le q eta rho m hq.1 heta hrho.1 hm
  have hhu : h ∈ Ioc (0 : ℝ) (1-q) := rootSmoothingWidth_mem q eta rho m hq heta hrho.1 hm
  have hqu : q ∈ Ioo (0 : ℝ) 1 := ⟨hq.1,by linarith [hq.2]⟩
  have hs : lam/beta ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hlam.1 hbeta.le,(div_le_one hbeta).mpr hlam.2⟩
  let bar := partialReflectedParisiMeasure μ (lam/beta) q h hs hh.1
  have hbudget := rootSmoothingWidth_budget q eta rho m hq.1 heta hrho.1 hm
  refine ⟨hm,hmv,hh.1,hh.2,hbudget,
    rootSmoothingWidth_inverse_bound q eta rho m hq.1 heta hrho.1 hm,bar,?_,?_,?_,?_,?_⟩
  · rw [mem_scalarFloor_iff,partialReflectedParisiMeasure_root μ (lam/beta) q h hs hqu hhu]
  · rw [partial_reflected_energy_root beta μ (lam/beta) q h hs hqu hhu]
    field_simp
  · exact followupMinimizer_partial_budget n hn beta lam rho q h eta hbeta hlam
      ⟨hrho.1.le,hrho.2⟩ hqu hhu hbudget
  · exact partial_reflected_energy_profile_below beta lam q h hbeta hlam μ hh.1
  · exact partial_reflected_interior_density_le beta hbeta.le μ (lam/beta) q h (q/4) (3*q/4)
      hs hqu hhu (by linarith [hq.1]) (by linarith [hq.1])

end QuantitativeFollowup
