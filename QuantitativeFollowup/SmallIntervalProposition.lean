module
public import QuantitativeFollowup.SmallIntervalIntegratedModel

@[expose] public section

/-! Literal follow-up Proposition8.1: one temperature-only constant works
for every actual minimizing profile and the native optimized integral,
independently of all profile atoms and their positions. -/
noncomputable section
open Set Filter MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 2200000

def SmallIntervalTarget (β : ℝ) (hβ : 1<β) : Prop :=
  ∃C : ℝ,0<C ∧
    (∀n : ℕ,∀hn : 2  ≤  n,∀μ : Paper.ParisiMeasure,∀lam rho eta : ℝ,
      ∀hlam : lam∈Ioc (0:ℝ) (min 1 (β/4)),∀hrho : rho∈Ioc (0:ℝ) 1,
      μ∈scalarFloor (lam/β)   →  
      (∀ν∈scalarFloor (lam/β),followupEnergyFunctional n β lam rho μ  ≤  
        followupEnergyFunctional n β lam rho ν)   →   0  ≤  eta   →  
      smallIntervalTrialGap n (by omega) β lam rho (zero_lt_one.trans hβ)
        ⟨hlam.1.le,by linarith [hlam.2.trans (min_le_right 1 (β/4))]⟩ hrho.1.le  ≤  eta   →  
      (β*vectorInterpolationDefect (n:=n) μ (lam/β) β (1-rho) (by linarith [hrho.1])  ≤  
        C*((Real.log (2+(n:ℝ)))^2/((n:ℝ)*rho*lam)+((n:ℝ)*rho)^(-(2/3:ℝ))+
          ((n:ℝ)*rho)^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*(smallIntervalOmega rho eta)^(2/3:ℝ))) ∧
      (β*vectorInterpolationDefect (n:=n) μ (lam/β) β (1-rho) (by linarith [hrho.1])  ≤  
        C*((n:ℝ)*rho)^(-(1/2:ℝ)))) ∧
    (∀n : ℕ,∀hn : 2 ≤ n,∀lam eta b : ℝ,
      ∀hlam : lam∈Ioc (0:ℝ) (min 1 (β/4)),∀hb : b∈Ioc (0:ℝ) 1,0 ≤ eta  → 
      (∀rho : ℝ,∀hrho : rho∈Ioc (0:ℝ) b,
        smallIntervalTrialGap n (by omega) β lam rho (zero_lt_one.trans hβ)
          ⟨hlam.1.le,by linarith [hlam.2.trans (min_le_right 1 (β/4))]⟩ hrho.1.le ≤ eta)  → 
      IntervalIntegrable (smallIntervalDefect n β lam) volume 0 b ∧
      (∫rho in (0:ℝ)..b,smallIntervalDefect n β lam rho) ≤ 
        C*(1/(n:ℝ)+(Real.log (2+(n:ℝ)))^3/((n:ℝ)*lam)+
          (n:ℝ)^(-(2/3:ℝ))*b^(1/3:ℝ)+
          (n:ℝ)^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*eta^(1/9:ℝ)*b^(2/9:ℝ)))

 theorem small_interval_near_zero (β : ℝ) (hβ : 1<β) : SmallIntervalTarget β hβ := by
  obtain ⟨Cp,hCp,hProfile⟩:=small_interval_profile_bounds β hβ
  obtain ⟨Ci,hCi,hIntegral⟩:=small_interval_integrated_model β hβ
  refine ⟨Cp+Ci,add_pos hCp hCi,?_,?_⟩
  · intro n hn μ lam rho eta hlam hrho hμ hmin heta hBudget
    obtain ⟨hp,hm⟩:=hProfile n hn μ lam rho eta hlam hrho hμ hmin heta hBudget
    have hn0 : 0<n:=by omega
    have hnr : 0<(n:ℝ)*rho:=mul_pos (Nat.cast_pos.mpr hn0) hrho.1
    have homega:=smallIntervalOmega_nonneg rho eta hrho.1.le heta
    constructor
    · exact hp.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hCi.le) (by positivity [hlam.1,hrho.1]))
    · exact hm.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hCi.le) (by positivity [hrho.1]))
  · intro n hn lam eta b hlam hb heta hBudget
    obtain ⟨hi,hh⟩:=hIntegral n hn lam eta b hlam hb heta hBudget
    refine ⟨hi,hh.trans ?_⟩
    apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCp.le)
    have hN : (1:ℝ) ≤ n:=by exact_mod_cast (show 1 ≤ n by omega)
    simpa only [smallIntervalIntegratedBudget,one_div] using
      smallIntervalIntegratedBudget_nonneg (n:ℝ) lam eta b hN hlam.1 heta hb.1.le

end QuantitativeFollowup
