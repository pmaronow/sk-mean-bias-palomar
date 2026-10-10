module
public import QuantitativeFollowup.SmallIntervalModel

@[expose] public section

/-! Honest minimum differentiability and attained profiles identify the native
optimized energy defect almost everywhere in the reflected overlap clock. -/
noncomputable section
open Set Filter MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 2200000

 theorem smallIntervalDefect_intervalIntegrable (n : ℕ) (hn : 0<n)
    (β lam : ℝ) (hβ : 0<β) (hs : lam/β∈Ioo (0:ℝ) 1) :
    IntervalIntegrable (smallIntervalDefect n β lam) volume 0 1 := by
  have hh:=(vectorInterpolationMinimum_integral n hn β (lam/β) hs hβ.ne').1
  have hc:=hh.comp_sub_left 1
  norm_num only [sub_zero,sub_self] at hc
  exact hc.symm.const_mul β

 theorem smallInterval_ae_differentiable (n : ℕ) (hn : 0<n) (β lam : ℝ)
    (hβ : 0<β) (hs : lam/β∈Ioo (0:ℝ) 1) :
    ∀ᵐrho : ℝ,rho∈Ioo (0:ℝ) 1 →
      DifferentiableAt ℝ (vectorInterpolationMinimum n β (lam/β)) (1-rho) := by
  have hh:=(volume.measurePreserving_sub_left 1).quasiMeasurePreserving.ae
    (vectorInterpolationMinimum_ae_differentiable n hn β (lam/β) hs hβ.ne')
  filter_upwards [hh] with rho hd
  intro hrho
  exact hd ⟨by linarith [hrho.2],by linarith [hrho.1]⟩

 theorem small_interval_optimized_bounds (β : ℝ) (hβ : 1<β) :
    ∃C : ℝ,0<C ∧ ∀n : ℕ,∀hn : 2≤n,∀lam : ℝ,
      ∀hlam : lam∈Ioc (0:ℝ) (min 1 (β/4)),∀eta : ℝ,0≤eta →
      ∀ᵐrho : ℝ,∀hrho : rho∈Ioo (0:ℝ) 1,
      smallIntervalTrialGap n (by omega) β lam rho (zero_lt_one.trans hβ)
        ⟨hlam.1.le,by linarith [hlam.2.trans (min_le_right 1 (β/4))]⟩ hrho.1.le ≤ eta →
      (smallIntervalDefect n β lam rho ≤
        C*((Real.log (2+(n:ℝ)))^2/((n:ℝ)*rho*lam)+((n:ℝ)*rho)^(-(2/3:ℝ))+
          ((n:ℝ)*rho)^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*(smallIntervalOmega rho eta)^(2/3:ℝ))) ∧
      (smallIntervalDefect n β lam rho ≤ C*((n:ℝ)*rho)^(-(1/2:ℝ))) := by
  obtain ⟨C,hC,hAll⟩:=small_interval_profile_bounds β hβ
  refine ⟨C,hC,?_⟩
  intro n hn lam hlam eta heta
  have hn0 : 0<n:=by omega
  have hβp : 0<β:=zero_lt_one.trans hβ
  have hs : lam/β∈Ioo (0:ℝ) 1:=⟨div_pos hlam.1 hβp,(div_lt_one hβp).mpr
    (by linarith [hlam.2.trans (min_le_right 1 (β/4))])⟩
  filter_upwards [smallInterval_ae_differentiable n hn0 β lam hβp hs] with rho hd
  intro hrho hBudget
  let μ:=vectorMeasureMinimizer n hn0 β (1-rho) (lam/β) (by linarith [hrho.1]) hs.2.le
  have hμ:=vectorMeasureMinimizer_mem n hn0 β (1-rho) (lam/β) (by linarith [hrho.1]) hs.2.le
  have hmin:=vectorMeasureMinimizer_minimal n hn0 β (1-rho) (lam/β) (by linarith [hrho.1]) hs.2.le
  have hminE : ∀ν∈scalarFloor (lam/β),followupEnergyFunctional n β lam rho μ ≤
      followupEnergyFunctional n β lam rho ν :=
    fun ν hν => div_le_div_of_nonneg_right (hmin ν hν) hβp.le
  have hb:=hAll n hn μ lam rho eta hlam ⟨hrho.1,hrho.2.le⟩ hμ hminE heta hBudget
  unfold smallIntervalDefect
  rw [optimizedVectorInterpolationDefect_eq_of_minimizer hn0 μ β (lam/β) hs hμ hβp.ne'
    (1-rho) ⟨by linarith [hrho.2],by linarith [hrho.1]⟩ hmin (hd hrho)]
  exact hb

end QuantitativeFollowup
