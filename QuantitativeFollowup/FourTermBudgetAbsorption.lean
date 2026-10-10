module
public import QuantitativeFollowup.FourTermBudgetPowers

@[expose] public section

/-! The exact two-exponent absorption giving all four source budget powers.
This is a pure supporting inequality; the native model supplies its input. -/
noncomputable section
open Set
open scoped BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 2200000

def fourTermBudgetYoungFirst : ℝ := (20/21:ℝ)*(4/21:ℝ)^(1/20:ℝ)
def fourTermBudgetYoungSecond : ℝ := (6/7:ℝ)*(4/7:ℝ)^(1/6:ℝ)
def fourTermBudgetAbsorptionConstant (C L : ℝ) : ℝ :=
  2*C+2*C*L^(1/21:ℝ)+2*C*L^(1/7:ℝ)+
    2*fourTermBudgetYoungFirst*C^(21/20:ℝ)+2*fourTermBudgetYoungSecond*C^(7/6:ℝ)+1

def fourTermBudgetRate (N lam : ℝ) : ℝ :=
  N^(-(7/10:ℝ))+N^(-(2/3:ℝ))*lam^(5/21:ℝ)+
    N^(-(7/9:ℝ))*lam^(-(7/18:ℝ))+(Real.log (2+N))^3/(N*lam^(12/7:ℝ))

 theorem fourTermBudgetAbsorptionConstant_pos (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    0<fourTermBudgetAbsorptionConstant C L := by
  unfold fourTermBudgetAbsorptionConstant fourTermBudgetYoungFirst fourTermBudgetYoungSecond
  positivity

 theorem fourTermBudgetRate_nonneg (N lam : ℝ) (hN : 1 ≤ N) (hlam : 0<lam) :
    0 ≤ fourTermBudgetRate N lam := by
  have hNp : 0<N:=zero_lt_one.trans_le hN
  have hl : 0 ≤ Real.log (2+N):=Real.log_nonneg (by linarith)
  unfold fourTermBudgetRate
  positivity

 theorem fourTermBudget_absorption (N lam e C L : ℝ) (hN : 1 ≤ N)
    (hlam : lam∈Ioc (0:ℝ) 1) (he : 0 ≤ e) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hinput : e ≤ C*(Real.log (2+N))^3/(N*lam^(12/7:ℝ))+
      (C*N^(-(2/3:ℝ)))*(e+L*lam^5)^(1/21:ℝ)+
      (C*N^(-(2/3:ℝ))*lam^(-(1/3:ℝ)))*(e+L*lam^5)^(1/7:ℝ)) :
    e ≤ fourTermBudgetAbsorptionConstant C L*fourTermBudgetRate N lam := by
  have hNp : 0<N:=zero_lt_one.trans_le hN
  let G:=(Real.log (2+N))^3/(N*lam^(12/7:ℝ))
  let U:=N^(-(7/10:ℝ))
  let V:=N^(-(2/3:ℝ))*lam^(5/21:ℝ)
  let W:=N^(-(7/9:ℝ))*lam^(-(7/18:ℝ))
  let A : Fin 2  →  ℝ:=fun i=>if i=0 then C*N^(-(2/3:ℝ)) else C*N^(-(2/3:ℝ))*lam^(-(1/3:ℝ))
  let h : Fin 2  →  ℝ:=fun i=>if i=0 then (1/21:ℝ) else (1/7:ℝ)
  have hG : 0 ≤ G:=by
    have hl : 0 ≤ Real.log (2+N):=Real.log_nonneg (by linarith)
    dsimp only [G];positivity [hlam.1]
  have hU : 0 ≤ U:=Real.rpow_nonneg hNp.le _
  have hV : 0 ≤ V:=by dsimp only [V];positivity [hlam.1]
  have hW : 0 ≤ W:=by dsimp only [W];positivity [hlam.1]
  have hΛ : 0 ≤ L*lam^5:=mul_nonneg hL (pow_nonneg hlam.1.le _)
  have hA : ∀i,0 ≤ A i:=by intro i;fin_cases i <;> simp only [A] <;> positivity [hlam.1]
  have hh : ∀i,h i∈Ioo (0:ℝ) 1:=by intro i;fin_cases i <;> norm_num [h]
  have hbound : e ≤ C*G+∑i,A i*(e+L*lam^5)^(h i) := by
    norm_num only [A,h,Fin.sum_univ_two,Fin.isValue,ite_true,ite_false,
      zero_ne_one,one_ne_zero] 
    convert hinput using 1 <;> dsimp only [G] <;> ring
  have hy:=absorption A h he hΛ (mul_nonneg hC hG) hA hh hbound
  norm_num [A,h,Fin.sum_univ_two] at hy
  rw [fourTermBudget_first_trial_power N lam C L hNp hlam.1 hC hL,
    fourTermBudget_first_young_power N C hNp.le hC,
    fourTermBudget_second_young_power N lam C hNp.le hlam.1.le hC] at hy
  have hsecond:=fourTermBudget_second_trial_le N lam C L hNp hlam hC hL
  have hR1 : 0 ≤ fourTermBudgetYoungFirst:=by unfold fourTermBudgetYoungFirst;positivity
  have hR2 : 0 ≤ fourTermBudgetYoungSecond:=by unfold fourTermBudgetYoungSecond;positivity
  have hn : e ≤ (2*C)*G+(2*C*L^(1/21:ℝ)+2*C*L^(1/7:ℝ))*V+
      (2*fourTermBudgetYoungFirst*C^(21/20:ℝ))*U+
      (2*fourTermBudgetYoungSecond*C^(7/6:ℝ))*W := by
    dsimp only [G,U,V,W,fourTermBudgetYoungFirst,fourTermBudgetYoungSecond]
    dsimp only [G] at hy
    nlinarith only [hy,hsecond]
  let B:=fourTermBudgetAbsorptionConstant C L
  have hp0 : 0 ≤ 2*C:=mul_nonneg (by norm_num) hC
  have hp1 : 0 ≤ 2*C*L^(1/21:ℝ)+2*C*L^(1/7:ℝ):=by positivity
  have hp2 : 0 ≤ 2*fourTermBudgetYoungFirst*C^(21/20:ℝ):=by positivity
  have hp3 : 0 ≤ 2*fourTermBudgetYoungSecond*C^(7/6:ℝ):=by positivity
  have h0 : 2*C ≤ B:=by dsimp only [B,fourTermBudgetAbsorptionConstant];linarith
  have h1 : 2*C*L^(1/21:ℝ)+2*C*L^(1/7:ℝ) ≤ B:=by dsimp only [B,fourTermBudgetAbsorptionConstant];linarith
  have h2 : 2*fourTermBudgetYoungFirst*C^(21/20:ℝ) ≤ B:=by dsimp only [B,fourTermBudgetAbsorptionConstant];linarith
  have h3 : 2*fourTermBudgetYoungSecond*C^(7/6:ℝ) ≤ B:=by dsimp only [B,fourTermBudgetAbsorptionConstant];linarith
  have hfinal:=add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right h0 hG) (mul_le_mul_of_nonneg_right h1 hV))
    (mul_le_mul_of_nonneg_right h2 hU)) (mul_le_mul_of_nonneg_right h3 hW)
  apply hn.trans
  convert hfinal using 1 <;> dsimp only [fourTermBudgetRate,U,V,W,G,B] <;> ring

end QuantitativeFollowup
