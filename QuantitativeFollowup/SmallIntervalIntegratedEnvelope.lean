module
public import QuantitativeFollowup.SmallIntervalIntegralBudget

@[expose] public section

/-! Genuine integration of the pointwise and moving envelopes, split at
1/N. This supporting theorem is instantiated by the actual minimum next. -/
noncomputable section
open Set Filter MeasureTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 2000000

def smallIntervalIntegratedBudget (N lam eta b : ℝ) : ℝ :=
  N⁻¹+(Real.log (2+N))^3/(N*lam)+N^(-(2/3:ℝ))*b^(1/3:ℝ)+
    N^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*eta^(1/9:ℝ)*b^(2/9:ℝ)

 theorem smallIntervalIntegratedBudget_nonneg (N lam eta b : ℝ)
    (hN : 1 ≤ N) (hlam : 0<lam) (heta : 0 ≤ eta) (hb : 0 ≤ b) :
    0 ≤ smallIntervalIntegratedBudget N lam eta b := by
  have hNp : 0<N:=zero_lt_one.trans_le hN
  have hl : 0 ≤ Real.log (2+N):=Real.log_nonneg (by linarith)
  unfold smallIntervalIntegratedBudget
  positivity

 theorem smallInterval_integrated_envelope (N lam eta C b : ℝ) (hN : 1 ≤ N)
    (hlam : 0<lam) (heta : 0 ≤ eta) (hC : 0 ≤ C) (hb : b∈Ioc (0:ℝ) 1)
    (f : ℝ  →  ℝ) (hf : IntervalIntegrable f volume 0 b)
    (hpoint : ∀ᵐrho∂volume.restrict (Ioo (0:ℝ) b),f rho ≤ 
      C*((Real.log (2+N))^2/(N*rho*lam)+(N*rho)^(-(2/3:ℝ))+
        (N*rho)^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*(smallIntervalOmega rho eta)^(2/3:ℝ)))
    (hmove : ∀ᵐrho∂volume.restrict (Ioo (0:ℝ) b),f rho ≤ C*(N*rho)^(-(1/2:ℝ))) :
    (∫rho in (0:ℝ)..b,f rho) ≤ 6*C*smallIntervalIntegratedBudget N lam eta b := by
  have hNp : 0<N:=zero_lt_one.trans_le hN
  have hcut : 0<1/N:=by positivity
  let X:=N⁻¹
  let Y:=(Real.log (2+N))^3/(N*lam)
  let Z:=N^(-(2/3:ℝ))*b^(1/3:ℝ)
  let W:=N^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*eta^(1/9:ℝ)*b^(2/9:ℝ)
  have hX : 0 ≤ X:=by dsimp only [X];positivity
  have hY : 0 ≤ Y:=by
    have hl : 0 ≤ Real.log (2+N):=Real.log_nonneg (by linarith)
    dsimp only [Y];positivity
  have hZ : 0 ≤ Z:=by dsimp only [Z];positivity [hb.1]
  have hW : 0 ≤ W:=by dsimp only [W];positivity [hb.1]
  change _ ≤ 6*C*(X+Y+Z+W)
  by_cases hsmall : b ≤ 1/N
  · have hh:=smallInterval_moving_integral_le N C b hNp hC hb.1.le hsmall f hf hmove
    have hp:=mul_nonneg hC (by linarith : 0 ≤ 4*X+6*Y+6*Z+6*W)
    dsimp only [X] at hp ⊢
    simp only [div_eq_mul_inv] at hh hp ⊢
    nlinarith only [hh,hp]
  · have hlarge : 1/N ≤ b:=(lt_of_not_ge hsmall).le
    have hsub0 : uIcc (0:ℝ) (1/N)⊆uIcc (0:ℝ) b:=by
      rw [uIcc_of_le hcut.le,uIcc_of_le hb.1.le]
      exact Icc_subset_Icc le_rfl hlarge
    have hsub1 : uIcc (1/N:ℝ) b⊆uIcc (0:ℝ) b:=by
      rw [uIcc_of_le hlarge,uIcc_of_le hb.1.le]
      exact Icc_subset_Icc hcut.le le_rfl
    have hm : ∀ᵐrho∂volume.restrict (Ioo (0:ℝ) (1/N)),f rho ≤ C*(N*rho)^(-(1/2:ℝ)):=
      hmove.filter_mono (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo le_rfl hlarge) le_rfl))
    have hp : ∀ᵐrho∂volume.restrict (Ioo (1/N:ℝ) b),f rho ≤ 
        C*((Real.log (2+N))^2/(N*rho*lam)+(N*rho)^(-(2/3:ℝ))+
          (N*rho)^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*(smallIntervalOmega rho eta)^(2/3:ℝ)):=
      hpoint.filter_mono (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo hcut.le le_rfl) le_rfl))
    have hearly:=smallInterval_moving_integral_le N C (1/N) hNp hC hcut.le le_rfl f (hf.mono_set hsub0) hm
    have hlate:=smallInterval_late_integral_le N lam eta C b hN hlam heta hC hb.2 hlarge f (hf.mono_set hsub1) hp
    rw [←intervalIntegral.integral_add_adjacent_intervals (hf.mono_set hsub0) (hf.mono_set hsub1)]
    have hh:=add_le_add hearly hlate
    change _ ≤ _ at hh
    have hpos:=mul_nonneg hC (by linarith : 0 ≤ 4*X+5*Y+3*Z+(3/2:ℝ)*W)
    dsimp only [X,Y,Z,W] at hh hpos ⊢
    simp only [div_eq_mul_inv] at hh hpos ⊢
    nlinarith only [hh,hpos]

end QuantitativeFollowup
