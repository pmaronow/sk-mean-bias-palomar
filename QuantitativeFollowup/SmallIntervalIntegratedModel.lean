module
public import QuantitativeFollowup.SmallIntervalIntegratedEnvelope

@[expose] public section

/-! The actual native optimized energy defect on a small overlap interval.
Every envelope premise is discharged from actual minimizing profiles and
the literal clipped-trial budget; endpoint integrability is genuine. -/
noncomputable section
open Set Filter MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000

 theorem small_interval_integrated_model (β : ℝ) (hβ : 1<β) :
    ∃C : ℝ,0<C ∧ ∀n : ℕ,∀hn : 2 ≤ n,∀lam eta b : ℝ,
      ∀hlam : lam∈Ioc (0:ℝ) (min 1 (β/4)),∀hb : b∈Ioc (0:ℝ) 1,0 ≤ eta  → 
      (∀rho : ℝ,∀hrho : rho∈Ioc (0:ℝ) b,
        smallIntervalTrialGap n (by omega) β lam rho (zero_lt_one.trans hβ)
          ⟨hlam.1.le,by linarith [hlam.2.trans (min_le_right 1 (β/4))]⟩ hrho.1.le ≤ eta)  → 
      IntervalIntegrable (smallIntervalDefect n β lam) volume 0 b ∧
      (∫rho in (0:ℝ)..b,smallIntervalDefect n β lam rho) ≤ 
        C*(1/(n:ℝ)+(Real.log (2+(n:ℝ)))^3/((n:ℝ)*lam)+
          (n:ℝ)^(-(2/3:ℝ))*b^(1/3:ℝ)+
          (n:ℝ)^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*eta^(1/9:ℝ)*b^(2/9:ℝ)) := by
  obtain ⟨C,hC,hAll⟩:=small_interval_optimized_bounds β hβ
  refine ⟨6*C,mul_pos (by norm_num) hC,?_⟩
  intro n hn lam eta b hlam hb heta hBudget
  have hn0 : 0<n:=by omega
  have hN : (1:ℝ) ≤ n:=by exact_mod_cast (show 1 ≤ n by omega)
  have hβp : 0<β:=zero_lt_one.trans hβ
  have hs : lam/β∈Ioo (0:ℝ) 1:=⟨div_pos hlam.1 hβp,(div_lt_one hβp).mpr
    (by linarith [hlam.2.trans (min_le_right 1 (β/4))])⟩
  have hf : IntervalIntegrable (smallIntervalDefect n β lam) volume 0 b:=
    (smallIntervalDefect_intervalIntegrable n hn0 β lam hβp hs).mono_set (by
      rw [uIcc_of_le hb.1.le,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hb.2)
  have hae : ∀ᵐrho∂volume.restrict (Ioo (0:ℝ) b),
      (smallIntervalDefect n β lam rho ≤ 
        C*((Real.log (2+(n:ℝ)))^2/((n:ℝ)*rho*lam)+((n:ℝ)*rho)^(-(2/3:ℝ))+
          ((n:ℝ)*rho)^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*(smallIntervalOmega rho eta)^(2/3:ℝ))) ∧
      (smallIntervalDefect n β lam rho ≤ C*((n:ℝ)*rho)^(-(1/2:ℝ))) := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hAll n hn lam hlam eta heta] with rho hr
    intro hrho
    have hunit : rho∈Ioo (0:ℝ) 1:=⟨hrho.1,hrho.2.trans_le hb.2⟩
    exact hr hunit (hBudget rho ⟨hrho.1,hrho.2.le⟩)
  refine ⟨hf,?_⟩
  have hh:=smallInterval_integrated_envelope (n:ℝ) lam eta C b hN hlam.1 heta hC.le hb
    (smallIntervalDefect n β lam) hf (hae.mono (fun _ h=>h.1)) (hae.mono (fun _ h=>h.2))
  simpa only [smallIntervalIntegratedBudget,one_div] using hh

end QuantitativeFollowup
