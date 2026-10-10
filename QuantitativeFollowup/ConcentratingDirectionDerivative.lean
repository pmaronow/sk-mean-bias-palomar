module
public import QuantitativeFollowup.VectorConcentratingCost

@[expose] public section

/-! The genuine first derivative in an actual concentrating direction.
The CDF relation specifies the direction; the derivative follows from the
closed actual vector first variation and the literal test pairing. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem hasDerivWithinAt_concentrating_energy_mix (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (beta lam rho a ell d : ℝ) (hbeta : 0 < beta) (hrho : 0 < rho)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell)
    (hprofile : ∀x, beta*parisiCDF ν x = beta*parisiCDF μ x-d*concentratingIntervalIncrement a ell x) :
    HasDerivWithinAt (fun theta => followupEnergyFunctional n beta lam rho (parisiMix μ ν theta))
      (rho*d/2*(vectorConcentratingDelta (n:=n) μ beta (1-rho) (lam/beta) (by linarith) a ell-8*ell/15))
      (Icc (0 : ℝ) 1) 0 := by
  have ht : 1-rho < 1 := by linarith
  have hCDF (x : ℝ) : parisiCDF ν x-parisiCDF μ x = -(d/beta)*concentratingIntervalIncrement a ell x := by
    have hp := hprofile x
    field_simp
    nlinarith
  have hp : (∫x in (0 : ℝ)..1, (parisiCDF ν x-parisiCDF μ x)*
      (vectorMeanOverlapReal (n:=n) μ beta (1-rho) (lam/beta) ht.le x-x)) =
      -(d/beta)*(8*ell/15-vectorConcentratingDelta (n:=n) μ beta (1-rho) (lam/beta) ht.le a ell) := by
    calc
      _ = -(d/beta)*(∫x in (0 : ℝ)..1, concentratingIntervalIncrement a ell x *
        (vectorMeanOverlapReal (n:=n) μ beta (1-rho) (lam/beta) ht.le x-x)) := by
        rw [←intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only
        rw [hCDF]
        ring
      _ = _ := by rw [vector_concentrating_pairing μ beta (1-rho) (lam/beta) hbeta.ne' ht a ell ha he hell]
  have hd := (hasDerivWithinAt_vectorMeasureFunctional_mix_moment hn μ ν beta (1-rho) (lam/beta) hbeta.ne' ht).div_const beta
  rw [hp] at hd
  convert hd using 1
  · rfl
  · field_simp
    ring

theorem concentrating_profile_curve_affine (A : ℝ → Paper.ParisiMeasure)
    (base : Paper.ParisiMeasure) (beta a ell l u : ℝ) (hbeta : 0 < beta)
    (hprofile : ∀tau∈Icc l u, ∀x,
      beta*parisiCDF (A tau) x=beta*parisiCDF base x-tau*concentratingIntervalIncrement a ell x)
    (v w theta : ℝ) (hv : v ∈ Icc l u) (hw : w ∈ Icc l u) (htheta : theta ∈ Icc (0 : ℝ) 1) :
    A ((1-theta)*v+theta*w)=parisiMix (A v) (A w) theta := by
  have hc : (1-theta)*v+theta*w ∈ Icc l u := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr htheta.2) (sub_nonneg.mpr hv.1),
      mul_nonneg htheta.1 (sub_nonneg.mpr hw.1),
      mul_nonneg (sub_nonneg.mpr htheta.2) (sub_nonneg.mpr hv.2),
      mul_nonneg htheta.1 (sub_nonneg.mpr hw.2)]
  apply FRSB.eq_of_parisiCDF_ae_eq
  apply Filter.Eventually.of_forall
  intro x
  have hvp := hprofile v hv x
  have hwp := hprofile w hw x
  have hcp := hprofile _ hc x
  have htwp := congrArg (fun z : ℝ => theta*z) hwp
  have htvp := congrArg (fun z : ℝ => (1-theta)*z) hvp
  rw [parisiCDF_mix _ _ theta x htheta]
  nlinarith

theorem hasDerivWithinAt_concentrating_profile_right (hn : 0 < n)
    (A : ℝ → Paper.ParisiMeasure) (base : Paper.ParisiMeasure)
    (beta lam rho a ell l u tau : ℝ) (hbeta : 0 < beta) (hrho : 0 < rho)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell)
    (hprofile : ∀v∈Icc l u, ∀x,
      beta*parisiCDF (A v) x=beta*parisiCDF base x-v*concentratingIntervalIncrement a ell x)
    (htau : tau ∈ Ico l u) :
    HasDerivWithinAt (fun v => followupEnergyFunctional n beta lam rho (A v))
      (rho/2*(vectorConcentratingDelta (n:=n) (A tau) beta (1-rho) (lam/beta) (by linarith) a ell-8*ell/15))
      (Icc tau u) tau := by
  have htu : tau < u := htau.2
  have hden : u-tau ≠ 0 := (sub_pos.mpr htu).ne'
  have hsub : ∀x, beta*parisiCDF (A u) x = beta*parisiCDF (A tau) x-(u-tau)*concentratingIntervalIncrement a ell x := by
    intro x
    rw [hprofile u ⟨htau.1.trans htu.le,le_rfl⟩ x, hprofile tau ⟨htau.1,htu.le⟩ x]
    ring
  have hd := hasDerivWithinAt_concentrating_energy_mix hn (A tau) (A u) beta lam rho a ell (u-tau)
    hbeta hrho ha he hell hsub
  let z := fun v : ℝ => (v-tau)/(u-tau)
  have hz0 : z tau = 0 := by dsimp only [z]; rw [sub_self,zero_div]
  have hz : HasDerivWithinAt z (1/(u-tau)) (Icc tau u) tau := by
    exact (((hasDerivAt_id tau).sub_const tau).div_const (u-tau)).hasDerivWithinAt
  have hmap : MapsTo z (Icc tau u) (Icc (0 : ℝ) 1) := by
    intro v hv
    exact ⟨div_nonneg (sub_nonneg.mpr hv.1) (sub_pos.mpr htu).le,
      (div_le_one (sub_pos.mpr htu)).mpr (by linarith [hv.2])⟩
  have hd' : HasDerivWithinAt
      (fun theta => followupEnergyFunctional n beta lam rho (parisiMix (A tau) (A u) theta))
      (rho*(u-tau)/2*(vectorConcentratingDelta (n:=n) (A tau) beta (1-rho) (lam/beta) (by linarith) a ell-8*ell/15))
      (Icc (0 : ℝ) 1) (z tau) := by simpa only [hz0] using hd
  have hc := hd'.comp tau hz hmap
  have hfn : ∀v∈Icc tau u,
      followupEnergyFunctional n beta lam rho (A v)=
        (fun theta => followupEnergyFunctional n beta lam rho (parisiMix (A tau) (A u) theta)) (z v) := by
    intro v hv
    have hθ := hmap hv
    have hA := concentrating_profile_curve_affine A base beta a ell l u hbeta hprofile tau u (z v)
      ⟨htau.1,htu.le⟩ ⟨htau.1.trans htu.le,le_rfl⟩ hθ
    have hid : (1-z v)*tau+z v*u=v := by dsimp only [z]; field_simp [hden]; ring
    rw [hid] at hA
    exact congrArg (followupEnergyFunctional n beta lam rho) hA
  have hc' := hc.congr_of_mem hfn ⟨le_rfl,htu.le⟩
  convert hc' using 1
  field_simp [hden]

theorem hasDerivWithinAt_concentrating_profile_left (hn : 0 < n)
    (A : ℝ → Paper.ParisiMeasure) (base : Paper.ParisiMeasure)
    (beta lam rho a ell l u tau : ℝ) (hbeta : 0 < beta) (hrho : 0 < rho)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell)
    (hprofile : ∀v∈Icc l u, ∀x,
      beta*parisiCDF (A v) x=beta*parisiCDF base x-v*concentratingIntervalIncrement a ell x)
    (htau : tau ∈ Ioc l u) :
    HasDerivWithinAt (fun v => followupEnergyFunctional n beta lam rho (A v))
      (rho/2*(vectorConcentratingDelta (n:=n) (A tau) beta (1-rho) (lam/beta) (by linarith) a ell-8*ell/15))
      (Icc l tau) tau := by
  have hlt : l < tau := htau.1
  have hden : tau-l ≠ 0 := (sub_pos.mpr hlt).ne'
  have hsub : ∀x, beta*parisiCDF (A l) x = beta*parisiCDF (A tau) x-(l-tau)*concentratingIntervalIncrement a ell x := by
    intro x
    rw [hprofile l ⟨le_rfl,hlt.le.trans htau.2⟩ x, hprofile tau ⟨hlt.le,htau.2⟩ x]
    ring
  have hd := hasDerivWithinAt_concentrating_energy_mix hn (A tau) (A l) beta lam rho a ell (l-tau)
    hbeta hrho ha he hell hsub
  let z := fun v : ℝ => (tau-v)/(tau-l)
  have hz0 : z tau = 0 := by dsimp only [z]; rw [sub_self,zero_div]
  have hz : HasDerivWithinAt z (-1/(tau-l)) (Icc l tau) tau := by
    exact (((hasDerivAt_id tau).const_sub tau).div_const (tau-l)).hasDerivWithinAt
  have hmap : MapsTo z (Icc l tau) (Icc (0 : ℝ) 1) := by
    intro v hv
    exact ⟨div_nonneg (sub_nonneg.mpr hv.2) (sub_pos.mpr hlt).le,
      (div_le_one (sub_pos.mpr hlt)).mpr (by linarith [hv.1])⟩
  have hd' : HasDerivWithinAt
      (fun theta => followupEnergyFunctional n beta lam rho (parisiMix (A tau) (A l) theta))
      (rho*(l-tau)/2*(vectorConcentratingDelta (n:=n) (A tau) beta (1-rho) (lam/beta) (by linarith) a ell-8*ell/15))
      (Icc (0 : ℝ) 1) (z tau) := by simpa only [hz0] using hd
  have hc := hd'.comp tau hz hmap
  have hfn : ∀v∈Icc l tau,
      followupEnergyFunctional n beta lam rho (A v)=
        (fun theta => followupEnergyFunctional n beta lam rho (parisiMix (A tau) (A l) theta)) (z v) := by
    intro v hv
    have hθ := hmap hv
    have hA := concentrating_profile_curve_affine A base beta a ell l u hbeta hprofile tau l (z v)
      ⟨hlt.le,htau.2⟩ ⟨le_rfl,hlt.le.trans htau.2⟩ hθ
    have hid : (1-z v)*tau+z v*l=v := by dsimp only [z]; field_simp [hden]; ring
    rw [hid] at hA
    exact congrArg (followupEnergyFunctional n beta lam rho) hA
  have hc' := hc.congr_of_mem hfn ⟨hlt.le,le_rfl⟩
  convert hc' using 1
  field_simp [hden]
  all_goals ring

end QuantitativeFollowup
