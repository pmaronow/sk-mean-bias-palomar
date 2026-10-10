module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Literal cutoff and stability arithmetic in the stable-interval proof.
These numerical leaves are applied to the actual minimizing model separately. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000

def stableIntervalCutoff (C eta : ℝ) : ℝ := min 1 (12*C*eta^((1:ℝ)/7))

theorem stableIntervalCutoff_bounds (C eta lam : ℝ) (hC : 1 ≤ C)
    (hlam : 0 < lam) (heta : lam^5 ≤ eta) :
    0 < stableIntervalCutoff C eta ∧
    min 1 (12*C*lam^((5:ℝ)/7)) ≤ stableIntervalCutoff C eta ∧
    stableIntervalCutoff C eta ≤ 12*C*eta^((1:ℝ)/7) := by
  have hetap : 0 < eta := (pow_pos hlam 5).trans_le heta
  have hp := Real.rpow_le_rpow (pow_nonneg hlam.le 5) heta
    (by norm_num : 0 ≤ (1:ℝ)/7)
  have he : (lam^5)^((1:ℝ)/7) = lam^((5:ℝ)/7) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hlam.le]
    congr 1
    norm_num
  rw [he] at hp
  refine ⟨lt_min zero_lt_one (by positivity),?_,min_le_right _ _⟩
  exact min_le_min le_rfl (mul_le_mul_of_nonneg_left hp (by positivity))

theorem stableIntervalCutoff_stability (C eta lam invN rho : ℝ)
    (hC : 1 ≤ C) (hlam : lam ∈ Ioc (0:ℝ) 1) (heta : lam^5 ≤ eta)
    (hN : invN ≤ lam) (hcut : stableIntervalCutoff C eta < 1)
    (hrho : stableIntervalCutoff C eta ≤ rho) :
    0 < rho ∧ invN ≤ rho ∧
    C*(rho^((-3:ℝ)/4)*eta^((1:ℝ)/4)+lam^2+invN) ≤ rho/4 := by
  let K := 12*C
  have hK : 1 ≤ K := by dsimp only [K]; linarith
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hetap : 0 < eta := (pow_pos hlam.1 5).trans_le heta
  have hsmall : K*eta^((1:ℝ)/7) < 1 := by
    by_contra hn
    have hh : 1 ≤ K*eta^((1:ℝ)/7) := le_of_not_gt hn
    simp only [stableIntervalCutoff,K,min_eq_left hh] at hcut
    exact lt_irrefl 1 hcut
  have hbase : K*eta^((1:ℝ)/7) ≤ rho := by
    simpa only [stableIntervalCutoff,K,min_eq_right hsmall.le] using hrho
  have hrp : 0 < rho := (mul_pos hKp (Real.rpow_pos_of_pos hetap _)).trans_le hbase
  have hp := Real.rpow_le_rpow (pow_nonneg hlam.1.le 5) heta
    (by norm_num : 0 ≤ (1:ℝ)/7)
  have he : (lam^5)^((1:ℝ)/7)=lam^((5:ℝ)/7) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hlam.1.le]
    congr 1
    norm_num
  rw [he] at hp
  have hkl : K*lam^((5:ℝ)/7) ≤ rho :=
    (mul_le_mul_of_nonneg_left hp hKp.le).trans hbase
  have hl1 : lam ≤ lam^((5:ℝ)/7) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hlam.1 hlam.2
        (by norm_num : (5:ℝ)/7 ≤ 1)
  have hl2 : lam^2 ≤ lam^((5:ℝ)/7) := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_ge hlam.1 hlam.2
        (by norm_num : (5:ℝ)/7 ≤ 2)
  have hterm2 : C*lam^2 ≤ rho/12 := by
    have hh := (mul_le_mul_of_nonneg_left hl2 hKp.le).trans hkl
    dsimp only [K] at hh
    linarith
  have hterm3 : C*invN ≤ rho/12 := by
    have hh := (mul_le_mul_of_nonneg_left (hN.trans hl1) hKp.le).trans hkl
    dsimp only [K] at hh
    linarith
  have hNρ : invN ≤ rho := by
    have hlamStrong : lam ≤ K*lam^((5:ℝ)/7) := hl1.trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hlam.1.le _) hK)
    exact hN.trans (hlamStrong.trans hkl)
  have hpower := Real.rpow_le_rpow
    (mul_nonneg hKp.le (Real.rpow_nonneg hetap.le _)) hbase
    (by norm_num : 0 ≤ (7:ℝ)/4)
  rw [Real.mul_rpow hKp.le (Real.rpow_nonneg hetap.le _),←Real.rpow_mul hetap.le] at hpower
  have hpowexp : (1:ℝ)/7*((7:ℝ)/4)=(1:ℝ)/4 := by norm_num
  rw [hpowexp] at hpower
  have hKpow : K ≤ K^((7:ℝ)/4) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hK (by norm_num : (1:ℝ) ≤ 7/4)
  have hpow : K*eta^((1:ℝ)/4) ≤ rho^((7:ℝ)/4) :=
    (mul_le_mul_of_nonneg_right hKpow (Real.rpow_nonneg hetap.le _)).trans hpower
  have hh := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hrp.le ((-3:ℝ)/4))
  have hrpow : rho^((7:ℝ)/4)*rho^((-3:ℝ)/4)=rho := by
    rw [←Real.rpow_add hrp]
    norm_num
  rw [hrpow] at hh
  have hterm1 : C*(rho^((-3:ℝ)/4)*eta^((1:ℝ)/4)) ≤ rho/12 := by
    dsimp only [K] at hh
    nlinarith only [hh]
  refine ⟨hrp,hNρ,?_⟩
  linarith

end QuantitativeFollowup
