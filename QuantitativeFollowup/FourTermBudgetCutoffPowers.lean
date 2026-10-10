module
public import QuantitativeFollowup.SmallIntervalIntegratedEnvelope
public import QuantitativeFollowup.FourTermBudgetAbsorption

@[expose] public section

/-! Converting the honest two interval integrals to the two Young terms.
The native model supplies both integrals and the actual cutoff bound. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

 theorem fourTermBudget_cutoff_powers (rho eta K : ℝ) (hrho : 0 ≤ rho)
    (heta : 0<eta) (hK : 0 ≤ K) (hcut : rho ≤ K*eta^(1/7:ℝ)) :
    rho^(1/3:ℝ) ≤ K^(1/3:ℝ)*eta^(1/21:ℝ) ∧
    eta^(1/9:ℝ)*rho^(2/9:ℝ) ≤ K^(2/9:ℝ)*eta^(1/7:ℝ) := by
  have h1:=Real.rpow_le_rpow hrho hcut (by norm_num : (0:ℝ) ≤ 1/3)
  rw [Real.mul_rpow hK (Real.rpow_nonneg heta.le _),←Real.rpow_mul heta.le] at h1
  norm_num at h1
  have h2:=Real.rpow_le_rpow hrho hcut (by norm_num : (0:ℝ) ≤ 2/9)
  rw [Real.mul_rpow hK (Real.rpow_nonneg heta.le _),←Real.rpow_mul heta.le] at h2
  norm_num at h2
  refine ⟨h1,?_⟩
  apply (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg heta.le _)).trans_eq
  calc
    _=K^(2/9:ℝ)*(eta^(1/9:ℝ)*eta^(2/63:ℝ)):=by ring
    _=_:=by rw [←Real.rpow_add heta];norm_num

 theorem fourTermBudget_log_bounds (N lam : ℝ) (hN : 2 ≤ N) (hlam : lam∈Ioc (0:ℝ) 1) :
    let G:=(Real.log (2+N))^3/(N*lam^(12/7:ℝ))
    1/N ≤ G ∧ (Real.log (2+N))^3/(N*lam) ≤ G ∧
      (Real.log (2+N))^2/(N*lam^(12/7:ℝ)) ≤ G := by
  have hNp : 0<N:=by linarith
  have hl4:=Real.log_le_log (by norm_num : (0:ℝ)<4) (by linarith : (4:ℝ) ≤ 2+N)
  rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hl4
  norm_num only [Nat.cast_ofNat] at hl4
  have hhalf : (1/2:ℝ)<Real.log 2:=lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog : 1 ≤ Real.log (2+N):=by linarith
  have hlog0 : 0≤Real.log (2+N):=zero_le_one.trans hlog
  have hp1 : lam^(12/7:ℝ) ≤ 1:=Real.rpow_le_one hlam.1.le hlam.2 (by norm_num)
  have hp2 : lam^(12/7:ℝ) ≤ lam:=by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hlam.1 hlam.2
      (by norm_num : (1:ℝ) ≤ 12/7)
  have hl2 : (Real.log (2+N))^2 ≤ (Real.log (2+N))^3:=by
    have hh:=mul_nonneg (sq_nonneg (Real.log (2+N))) (by linarith : 0 ≤ Real.log (2+N)-1)
    nlinarith only [hh]
  have hl3 : 1 ≤ (Real.log (2+N))^3:=by nlinarith [sq_nonneg (Real.log (2+N)-1)]
  have hd : 0<N*lam^(12/7:ℝ):=mul_pos hNp (Real.rpow_pos_of_pos hlam.1 _)
  dsimp only
  refine ⟨?_,?_,div_le_div_of_nonneg_right hl2 hd.le⟩
  · exact (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hd
      ((mul_le_mul_of_nonneg_left hp1 hNp.le).trans_eq (mul_one N))).trans
      (div_le_div_of_nonneg_right hl3 hd.le)
  · exact div_le_div_of_nonneg_left (by positivity : 0 ≤ (Real.log (2+N))^3) hd
      (mul_le_mul_of_nonneg_left hp2 hNp.le)

def fourTermBudgetInputConstant (Cs Ct K : ℝ) : ℝ :=
  Cs*(2+K^(1/3:ℝ)+K^(2/9:ℝ))+Ct+1

 theorem fourTermBudgetInputConstant_pos (Cs Ct K : ℝ) (hCs : 0 ≤ Cs) (hCt : 0 ≤ Ct) (hK : 0 ≤ K) :
    0<fourTermBudgetInputConstant Cs Ct K := by
  unfold fourTermBudgetInputConstant
  positivity

 theorem fourTermBudget_input_from_intervals (N lam e eta Cs Ct K rho : ℝ)
    (hN : 2 ≤ N) (hlam : lam∈Ioc (0:ℝ) 1) (he : 0 ≤ e) (heta : 0<eta)
    (hCs : 0 ≤ Cs) (hCt : 0 ≤ Ct) (hK : 0 ≤ K) (hrho : rho∈Ioc (0:ℝ) 1)
    (hcut : rho ≤ K*eta^(1/7:ℝ)) (f : ℝ  →  ℝ)
    (hwhole : 4*e=(∫r in (0:ℝ)..1,f r))
    (hf : IntervalIntegrable f volume 0 1)
    (hsmall : (∫r in (0:ℝ)..rho,f r) ≤ Cs*smallIntervalIntegratedBudget N lam eta rho)
    (hstable : rho<1  →  (∫r in rho..(1:ℝ),f r) ≤ Ct*(Real.log (2+N))^2/(N*lam^(12/7:ℝ))) :
    e ≤ fourTermBudgetInputConstant Cs Ct K*(Real.log (2+N))^3/(N*lam^(12/7:ℝ))+
      (fourTermBudgetInputConstant Cs Ct K*N^(-(2/3:ℝ)))*eta^(1/21:ℝ)+
      (fourTermBudgetInputConstant Cs Ct K*N^(-(2/3:ℝ))*lam^(-(1/3:ℝ)))*eta^(1/7:ℝ) := by
  have hNp : 0<N:=by linarith
  let G:=(Real.log (2+N))^3/(N*lam^(12/7:ℝ))
  let U:=N^(-(2/3:ℝ))*eta^(1/21:ℝ)
  let V:=N^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*eta^(1/7:ℝ)
  have hG : 0 ≤ G:=by
    have hl : 0 ≤ Real.log (2+N):=Real.log_nonneg (by linarith)
    dsimp only [G];positivity [hlam.1]
  have hU : 0 ≤ U:=by dsimp only [U];positivity
  have hV : 0 ≤ V:=by dsimp only [V];positivity [hlam.1]
  have hlog:=fourTermBudget_log_bounds N lam hN hlam
  have hp:=fourTermBudget_cutoff_powers rho eta K hrho.1.le heta hK hcut
  have hsb : (∫r in (0:ℝ)..rho,f r) ≤ Cs*(2*G+K^(1/3:ℝ)*U+K^(2/9:ℝ)*V) := by
    apply hsmall.trans
    apply mul_le_mul_of_nonneg_left _ hCs
    have h1:=mul_le_mul_of_nonneg_left hp.1 (Real.rpow_nonneg hNp.le (-(2/3:ℝ)))
    have h2:=mul_le_mul_of_nonneg_left hp.2
      (by positivity [hlam.1] : 0 ≤ N^(-(2/3:ℝ))*lam^(-(1/3:ℝ)))
    dsimp only [smallIntervalIntegratedBudget,U,V,G]
    have hh:=add_le_add (add_le_add (add_le_add hlog.1 hlog.2.1) h1) h2
    convert hh using 1 <;> ring
  have htb : (∫r in rho..(1:ℝ),f r) ≤ Ct*G := by
    rcases lt_or_eq_of_le hrho.2 with hlt|heq
    · have hb:=hstable hlt
      apply hb.trans
      convert mul_le_mul_of_nonneg_left hlog.2.2 hCt using 1 <;> ring
    · subst rho
      simp only [intervalIntegral.integral_same]
      exact mul_nonneg hCt hG
  have h0 : IntervalIntegrable f volume 0 rho:=hf.mono_set (by
    rw [uIcc_of_le zero_le_one,uIcc_of_le hrho.1.le]
    exact Icc_subset_Icc le_rfl hrho.2)
  have h1 : IntervalIntegrable f volume rho 1:=hf.mono_set (by
    rw [uIcc_of_le zero_le_one,uIcc_of_le hrho.2]
    exact Icc_subset_Icc hrho.1.le le_rfl)
  rw [←intervalIntegral.integral_add_adjacent_intervals h0 h1] at hwhole
  have hfour : e ≤ Cs*(2*G+K^(1/3:ℝ)*U+K^(2/9:ℝ)*V)+Ct*G := by linarith only [he,hwhole,hsb,htb]
  let C:=fourTermBudgetInputConstant Cs Ct K
  have hpk : 0 ≤ K^(1/3:ℝ):=Real.rpow_nonneg hK _
  have hqk : 0 ≤ K^(2/9:ℝ):=Real.rpow_nonneg hK _
  have hcp:=mul_nonneg hCs hpk
  have hcq:=mul_nonneg hCs hqk
  have h0C : 2*Cs+Ct ≤ C:=by dsimp only [C,fourTermBudgetInputConstant];nlinarith
  have h1C : Cs*K^(1/3:ℝ) ≤ C:=by dsimp only [C,fourTermBudgetInputConstant];nlinarith
  have h2C : Cs*K^(2/9:ℝ) ≤ C:=by dsimp only [C,fourTermBudgetInputConstant];nlinarith
  have hcg:=mul_le_mul_of_nonneg_right h0C hG
  have hcu:=mul_le_mul_of_nonneg_right h1C hU
  have hcv:=mul_le_mul_of_nonneg_right h2C hV
  have hh : e ≤ C*G+C*U+C*V:=by nlinarith only [hfour,hcg,hcu,hcv]
  convert hh using 1 <;> dsimp only [C,G,U,V] <;> ring

end QuantitativeFollowup
