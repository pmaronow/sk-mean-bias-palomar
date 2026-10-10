module
public import QuantitativePaper.UniformScalarTrialCost
public import QuantitativePaper.UniformScalarSmoothingHessian
public import QuantitativePaper.ScalarSupportEndpointLower

@[expose] public section

/-! Uniform actual fifth-order scalar trial cost from a genuine uniform
root-growth family. The explicit root-family input is discharged separately
by UniformScalarRootGrowth; this backend asserts no numbered completion. -/
noncomputable section
open Set MeasureTheory Paper FRSB QuantitativeFollowup
namespace QuantitativePaper
set_option maxHeartbeats 2300000

theorem scalar_clipped_trial_uniform_fifth_order_of_root_growth
    (β₀ : ℝ) (hβ₀ : 1<β₀) (k Tstar : ℝ) (hk : 0<k)
    (hTs : Tstar∈Ioc (0:ℝ) (1/4))
    (hgrowth : ∀β,β₀≤β→∀μ,IsParisiMinimizer β 0 μ→
      ∀q∈Icc (0:ℝ) Tstar,k*q≤β*parisiCDF μ q) :
    ∃C1 lamstar : ℝ,1≤C1 ∧ 0<lamstar ∧ lamstar≤1 ∧ lamstar≤β₀/2 ∧
      lamstar≤k*Tstar ∧ ∀β,β₀≤β→∀μ,IsParisiMinimizer β 0 μ→
      ∀lam∈Icc (0:ℝ) lamstar,∃hs : lam/β∈Icc (0:ℝ) 1,
        0 ≤ scalarEnergyValue β lam-scalarEnergyValue β 0 ∧
        scalarEnergyValue β lam-scalarEnergyValue β 0≤
          parisiPDEFunctional β 0 (scalarClippedTrialMeasure (lam/β) hs μ)/β-scalarEnergyValue β 0 ∧
        parisiPDEFunctional β 0 (scalarClippedTrialMeasure (lam/β) hs μ)/β-scalarEnergyValue β 0≤C1*lam^5 := by
  have hβ₀pos : 0<β₀ := zero_lt_one.trans hβ₀
  have hdist : 0<1-1/β₀ := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ hβ₀pos).mpr
    simpa using hβ₀
  obtain ⟨C,hC,hH⟩:=scalarEnergy_minimizer_hessian_uniform_early
  let A:=scalarUniformClippingConstant C 32
  let C1:=max 1 (A/k^3)
  let lamstar:=min 1 (min (β₀/2) (min (k*Tstar/2) (k*(1-1/β₀)/2)))
  have hA : 0<A := by dsimp [A,scalarUniformClippingConstant];positivity
  have hlamstar : 0<lamstar := lt_min zero_lt_one (lt_min (half_pos hβ₀pos)
    (lt_min (half_pos (mul_pos hk hTs.1)) (half_pos (mul_pos hk hdist))))
  have hls1 : lamstar≤1 := min_le_left _ _
  have hlsβ : lamstar≤β₀/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hlsT : lamstar≤k*Tstar/2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hlsq : lamstar≤k*(1-1/β₀)/2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨C1,lamstar,le_max_left _ _,hlamstar,hls1,hlsβ,
    hlsT.trans (half_le_self (mul_pos hk hTs.1).le),?_⟩
  intro β hb μ hmin lam hlam
  have hβ1 : 1<β := hβ₀.trans_le hb
  have hβ : 0<β := zero_lt_one.trans hβ1
  have hlamβ : lam≤β := by linarith [hlam.2.trans hlsβ]
  have hs : lam/β∈Icc (0:ℝ) 1 := ⟨div_nonneg hlam.1 hβ.le,
    (div_le_iff₀ hβ).mpr (by simpa using hlamβ)⟩
  have hbase : scalarEnergyValue β 0=parisiPDEFunctional β 0 μ/β :=
    scalarEnergyValue_zero_of_minimizer β μ hmin
  refine ⟨hs,?_,?_,?_⟩
  · unfold scalarEnergyValue
    simp only [zero_div]
    exact sub_nonneg.mpr (div_le_div_of_nonneg_right
      (constrainedParisiValue_mono β hs.1 hs.2) hβ.le)
  · have hh:=constrainedParisiValue_le β (lam/β) hs.2
      (scalarClippedTrialMeasure (lam/β) hs μ) (scalarClippedTrialMeasure_mem_floor (lam/β) hs μ)
    exact sub_le_sub_right (div_le_div_of_nonneg_right hh hβ.le) _
  · rw [hbase]
    obtain ⟨q,hq,hsupp⟩:=minimizer_full_support β hβ1 μ hmin
    by_cases hlam0 : lam=0
    · subst lam
      have he:=scalarClipped_functional_cost_integral 0 ⟨le_rfl,zero_le_one⟩ β hβ.ne' μ hmin
        q hq hsupp 0 le_rfl hq.1 (parisiCDF_nonneg μ 0)
      have he0 : parisiPDEFunctional β 0 (scalarClippedTrialMeasure (0/β) hs μ)-
          parisiPDEFunctional β 0 μ=0 := by simpa only [zero_div,intervalIntegral.integral_same] using he
      have hh:=div_le_div_of_nonneg_right he0.le hβ.le
      simpa only [sub_div,zero_div,zero_pow (by omega : 5≠0),mul_zero] using hh
    have hlamp : 0<lam := lt_of_le_of_ne hlam.1 (Ne.symm hlam0)
    have hqSupport : q∈parisiSupport μ := by rw [hsupp];exact ⟨hq.1.le,le_rfl⟩
    have hqLower:=scalar_support_max_ge_one_sub_inv β hβ μ hmin q hqSupport
      (fun x hx=>by rw [hsupp] at hx;exact hx.2)
    have hrec : 1/β≤1/β₀ := one_div_le_one_div_of_le hβ₀pos hb
    let T:=lam/k
    have hT : 0<T := div_pos hlamp hk
    have hTstar : T≤Tstar/2 := by
      apply (div_le_iff₀ hk).mpr
      have hh:=hlam.2.trans hlsT
      nlinarith
    have hTq : T<q := by
      have hh:=hlam.2.trans hlsq
      have hTT : T≤(1-1/β₀)/2 := by apply (div_le_iff₀ hk).mpr; nlinarith
      linarith
    have hTquarter : T≤1/4 := hTstar.trans ((half_le_self hTs.1.le).trans hTs.2)
    have hfloor : lam/β≤parisiCDF μ T := by
      have hh:=hgrowth β hb μ hmin T ⟨hT.le,hTstar.trans (half_le_self hTs.1.le)⟩
      have he : k*T=lam := by dsimp [T];field_simp
      rw [he] at hh
      exact (div_le_iff₀ hβ).mpr (by simpa only [mul_comm] using hh)
    have hcoeff (t:ℝ) (ht:t∈Icc (0:ℝ) T) : β*parisiCDF μ t≤32 :=
      scalarEnergy_sublevel_two_cdf_le β hβ μ
        ((scalarEnergy_minimizer_cost_lt_three_halves β hβ1.le μ hmin).le.trans (by norm_num)) t
        (ht.2.trans (hTquarter.trans (by norm_num)))
    have hc:=scalarClipped_functional_uniform_energy_cost_le (lam/β) hs β hβ μ hmin q hq hsupp
      lam C 32 T (mul_div_cancel₀ lam hβ.ne')
      (hlam.2.trans (hls1.trans (by norm_num))) ((by norm_num : (0:ℝ)≤1).trans hC)
      (by norm_num) hT hTq hfloor hcoeff
      (fun t ht x=>hH β hβ1.le μ hmin t ⟨ht.1,ht.2.trans hTquarter⟩ x)
    have he : A*lam^2*T^3=(A/k^3)*lam^5 := by dsimp [T];simp only [div_eq_mul_inv];ring
    change _≤A*lam^2*T^3 at hc
    rw [he] at hc
    have hc' : parisiPDEFunctional β 0 (scalarClippedTrialMeasure (lam/β) hs μ)/β-
        parisiPDEFunctional β 0 μ/β≤(A/k^3)*lam^5 := by convert hc using 1 <;> ring
    exact hc'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hlam.1 5))

end QuantitativePaper
