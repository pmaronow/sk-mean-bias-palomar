module
public import QuantitativeFollowup.ConcentratingPushedContact

@[expose] public section

/-! Actual affine CDF curves are genuine weakly continuous probability
mixing segments. Their functional continuity and convexity follow from
the actual Parisi functional, not from supplied curve conclusions. -/
noncomputable section
open Set Filter MeasureTheory Paper QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1700000

theorem continuousOn_parisiMix (μ ν : Paper.ParisiMeasure) :
    ContinuousOn (parisiMix μ ν) (Icc (0 : ℝ) 1) := by
  intro theta htheta
  rw [ContinuousWithinAt,ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hcont : Continuous (fun x : ℝ =>
      (1-x)*(∫r, f r ∂(μ : Measure Paper.Overlap))+x*(∫r, f r ∂(ν : Measure Paper.Overlap))) := by
    fun_prop
  have hlim := hcont.continuousWithinAt (s:=Icc (0 : ℝ) 1) (x:=theta)
  rw [integral_parisiMix f.continuous μ ν theta htheta]
  apply hlim.tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (integral_parisiMix f.continuous μ ν x hx).symm

theorem affine_profile_curve_mix (P : ℝ → Paper.ParisiMeasure) (base : Paper.ParisiMeasure)
    (beta l u : ℝ) (psi : ℝ → ℝ) (hbeta : 0 < beta)
    (hProfile : ∀v∈Icc l u, ∀x, beta*parisiCDF (P v) x=beta*parisiCDF base x+v*psi x)
    (v w theta : ℝ) (hv : v ∈ Icc l u) (hw : w ∈ Icc l u) (htheta : theta ∈ Icc (0 : ℝ) 1) :
    P ((1-theta)*v+theta*w)=parisiMix (P v) (P w) theta := by
  have hParam : (1-theta)*v+theta*w ∈ Icc l u := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr htheta.2) (sub_nonneg.mpr hv.1),
      mul_nonneg htheta.1 (sub_nonneg.mpr hw.1),
      mul_nonneg (sub_nonneg.mpr htheta.2) (sub_nonneg.mpr hv.2),
      mul_nonneg htheta.1 (sub_nonneg.mpr hw.2)]
  apply FRSB.eq_of_parisiCDF_ae_eq
  apply Filter.Eventually.of_forall
  intro x
  have hC := hProfile _ hParam x
  have hV := congrArg (fun z : ℝ => (1-theta)*z) (hProfile v hv x)
  have hW := congrArg (fun z : ℝ => theta*z) (hProfile w hw x)
  rw [parisiCDF_mix _ _ theta x htheta]
  nlinarith

theorem continuousOn_affine_profile_curve (P : ℝ → Paper.ParisiMeasure) (base : Paper.ParisiMeasure)
    (beta : ℝ) (psi : ℝ → ℝ) (hbeta : 0 < beta)
    (hProfile : ∀v∈Icc (0 : ℝ) 1, ∀x, beta*parisiCDF (P v) x=beta*parisiCDF base x+v*psi x) :
    ContinuousOn P (Icc (0 : ℝ) 1) := by
  apply (continuousOn_parisiMix (P 0) (P 1)).congr
  intro theta htheta
  have hm := affine_profile_curve_mix P base beta 0 1 psi hbeta hProfile 0 1 theta
    (by norm_num) (by norm_num) htheta
  simpa only [mul_zero,mul_one,zero_add] using hm

theorem continuousOn_affine_profile_functional (n : ℕ) (hn : 0 < n)
    (P : ℝ → Paper.ParisiMeasure) (base : Paper.ParisiMeasure) (beta lam rho : ℝ)
    (psi : ℝ → ℝ) (hbeta : 0 < beta) (hrho : 0 ≤ rho)
    (hProfile : ∀v∈Icc (0 : ℝ) 1, ∀x, beta*parisiCDF (P v) x=beta*parisiCDF base x+v*psi x) :
    ContinuousOn (fun v => followupEnergyFunctional n beta lam rho (P v)) (Icc (0 : ℝ) 1) :=
  ((continuous_vectorMeasureFunctional n hn beta (1-rho) (lam/beta) (by linarith)).div_const beta).comp_continuousOn
    (continuousOn_affine_profile_curve P base beta psi hbeta hProfile)

theorem convexOn_affine_profile_functional (n : ℕ) (P : ℝ → Paper.ParisiMeasure)
    (base : Paper.ParisiMeasure) (beta lam rho : ℝ) (psi : ℝ → ℝ)
    (hbeta : 0 < beta) (hlam : 0 ≤ lam) (hrho : 0 ≤ rho)
    (hProfile : ∀v∈Icc (0 : ℝ) 1, ∀x, beta*parisiCDF (P v) x=beta*parisiCDF base x+v*psi x) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun v => followupEnergyFunctional n beta lam rho (P v)) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy c d hc hd hcd
  have hd1 : d ∈ Icc (0 : ℝ) 1 := ⟨hd,by linarith⟩
  have hc1 : 1-d=c := by linarith
  have hm := followupEnergyFunctional_mix_le (n:=n) (P x) (P y) beta lam rho d hbeta hlam hrho hd1
  rw [←affine_profile_curve_mix P base beta 0 1 psi hbeta hProfile x y d hx hy hd1,hc1] at hm
  exact hm

end QuantitativeFollowup
