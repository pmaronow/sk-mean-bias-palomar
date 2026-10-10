module
public import QuantitativeFollowup.ConcentratingDirectionDerivative

@[expose] public section

/-! Convexity and both one-sided derivatives of any actual admissible
concentrating profile segment. The segment relation specifies the profiles;
all convexity and derivative conclusions come from the actual functional. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem convexOn_concentrating_profile (A : ℝ → Paper.ParisiMeasure)
    (base : Paper.ParisiMeasure) (beta lam rho a ell l u : ℝ)
    (hbeta : 0 < beta) (hlam : 0 ≤ lam) (hrho : 0 ≤ rho)
    (hprofile : ∀v∈Icc l u, ∀x,
      beta*parisiCDF (A v) x=beta*parisiCDF base x-v*concentratingIntervalIncrement a ell x) :
    ConvexOn ℝ (Icc l u) (fun v => followupEnergyFunctional n beta lam rho (A v)) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy c d hc hd hcd
  have hd1 : d ∈ Icc (0 : ℝ) 1 := ⟨hd,by linarith⟩
  have hc1 : 1-d=c := by linarith
  have hm := vectorMeasureFunctional_mix_le n (A x) (A y) beta (1-rho)
    (by linarith) (lam/beta) (div_nonneg hlam hbeta.le) d hd1
  rw [←concentrating_profile_curve_affine A base beta a ell l u hbeta hprofile x y d hx hy hd1,
    hc1] at hm
  have hdiv := div_le_div_of_nonneg_right hm hbeta.le
  change vectorMeasureFunctional n (A (c*x+d*y)) beta (1-rho) (lam/beta)/beta ≤
    c*(vectorMeasureFunctional n (A x) beta (1-rho) (lam/beta)/beta)+
      d*(vectorMeasureFunctional n (A y) beta (1-rho) (lam/beta)/beta)
  convert hdiv using 1
  ring

/-- Literal concentrating-direction lemma, with actual probability
profiles and the paper's affine CDF direction. -/
theorem concentrating_direction (hn : 0 < n)
    (A : ℝ → Paper.ParisiMeasure) (base : Paper.ParisiMeasure)
    (beta lam rho a ell l u : ℝ) (hbeta : 0 < beta) (hlam : 0 ≤ lam) (hrho : 0 < rho)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell)
    (hprofile : ∀v∈Icc l u, ∀x,
      beta*parisiCDF (A v) x=beta*parisiCDF base x-v*concentratingIntervalIncrement a ell x) :
    ConvexOn ℝ (Icc l u) (fun v => followupEnergyFunctional n beta lam rho (A v)) ∧
    (∀tau∈Ico l u, HasDerivWithinAt (fun v => followupEnergyFunctional n beta lam rho (A v))
      (rho/2*(vectorConcentratingDelta (n:=n) (A tau) beta (1-rho) (lam/beta) (by linarith) a ell-8*ell/15))
      (Icc tau u) tau) ∧
    (∀tau∈Ioc l u, HasDerivWithinAt (fun v => followupEnergyFunctional n beta lam rho (A v))
      (rho/2*(vectorConcentratingDelta (n:=n) (A tau) beta (1-rho) (lam/beta) (by linarith) a ell-8*ell/15))
      (Icc l tau) tau) :=
  ⟨convexOn_concentrating_profile A base beta lam rho a ell l u hbeta hlam hrho.le hprofile,
    fun tau htau => hasDerivWithinAt_concentrating_profile_right hn A base beta lam rho a ell l u tau
      hbeta hrho ha he hell hprofile htau,
    fun tau htau => hasDerivWithinAt_concentrating_profile_left hn A base beta lam rho a ell l u tau
      hbeta hrho ha he hell hprofile htau⟩

end QuantitativeFollowup
