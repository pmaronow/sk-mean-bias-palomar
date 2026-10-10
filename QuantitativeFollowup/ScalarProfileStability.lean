module
public import QuantitativeFollowup.TrialIsolation
public import QuantitativeFollowup.ScalarClippedDistance

@[expose] public section

/-! The profile-distance clause of scalar stability, for every actual
constrained minimizer and actual scalar-trial budget. This is the literal
CDF L¹ estimate; response-operator domination is a separate result. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FRSB
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000

theorem scalar_profile_stability (beta : ℝ) (hbeta : 1<beta) :
    ∃C : ℝ,1≤C ∧
      ∀n : ℕ,∀hn : 0<n,∀μ : Paper.ParisiMeasure,∀lam rho eta : ℝ,
      ∀hlam : lam∈Icc (0 : ℝ) beta,∀hrho : rho∈Ioc (0 : ℝ) 1,
      μ∈scalarFloor (lam/beta)→
      (∀ν∈scalarFloor (lam/beta),followupEnergyFunctional n beta lam rho μ≤
        followupEnergyFunctional n beta lam rho ν)→
      0≤eta→
      let ν := scalarClippedTrialMeasure (lam/beta)
        ⟨div_nonneg hlam.1 (zero_lt_one.trans hbeta).le,
          (div_le_one (zero_lt_one.trans hbeta)).mpr hlam.2⟩ (parisiMinimizer beta 0)
      followupEnergyFunctional n beta lam rho ν≤
        followupEnergyMinimum n hn beta lam rho (zero_lt_one.trans hbeta) hlam.2 hrho.1.le+eta→
      parisiCDFDistance μ (parisiMinimizer beta 0)≤
        min 1 (C*(rho^((-3/4 : ℝ))*eta^((1/4 : ℝ))+lam^2)) := by
  have hb : 0<beta := zero_lt_one.trans hbeta
  obtain ⟨Ki,hKi,hi⟩ := scalar_trial_isolation beta hbeta
  obtain ⟨Kc,hKc,hc⟩ := scalar_clipped_distance beta hbeta
  let C := max 1 ((Ki+Kc)/beta)
  refine ⟨C,le_max_left _ _,?_⟩
  intro n hn μ lam rho eta hlam hrho hμ hmin heta
  dsimp only
  intro hbudget
  let hs : lam/beta∈Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hlam.1 hb.le,(div_le_one hb).mpr hlam.2⟩
  let scalar := parisiMinimizer beta 0
  let ν := scalarClippedTrialMeasure (lam/beta) hs scalar
  let A := rho^((-3/4 : ℝ))*eta^((1/4 : ℝ))
  have hA : 0≤A := mul_nonneg (Real.rpow_nonneg hrho.1.le _) (Real.rpow_nonneg heta _)
  have hIso : beta*parisiCDFDistance μ ν≤Ki*min 1 A :=
    hi n hn μ lam rho eta hlam hrho hμ hmin heta hbudget
  have hClip : beta*parisiCDFDistance scalar ν≤Kc*lam^2 :=
    hc scalar (isParisiMinimizer_selected beta 0) lam hlam
  have hTriangle := mul_le_mul_of_nonneg_left
    (FourPapersCommon.parisiCDFDistance_triangle μ ν scalar) hb.le
  rw [FourPapersCommon.parisiCDFDistance_symm ν scalar,mul_add] at hTriangle
  have hScaled : beta*parisiCDFDistance μ scalar≤(Ki+Kc)*(A+lam^2) := by
    have hI := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) A) hKi.le
    have hCross1 : 0≤Ki*lam^2 := mul_nonneg hKi.le (sq_nonneg lam)
    have hCross2 : 0≤Kc*A := mul_nonneg hKc.le hA
    nlinarith only [hTriangle,hIso,hClip,hI,hCross1,hCross2]
  have hDistance : parisiCDFDistance μ scalar≤((Ki+Kc)/beta)*(A+lam^2) := by
    apply (mul_le_mul_iff_right₀ hb).mp
    calc
      beta*parisiCDFDistance μ scalar≤(Ki+Kc)*(A+lam^2) := hScaled
      _=beta*(((Ki+Kc)/beta)*(A+lam^2)) := by field_simp
  have hFinal : parisiCDFDistance μ scalar≤C*(A+lam^2) :=
    hDistance.trans (mul_le_mul_of_nonneg_right (le_max_right 1 ((Ki+Kc)/beta))
      (add_nonneg hA (sq_nonneg lam)))
  exact le_min (FourPapersCommon.parisiCDFDistance_le_one μ scalar) hFinal

end QuantitativeFollowup
