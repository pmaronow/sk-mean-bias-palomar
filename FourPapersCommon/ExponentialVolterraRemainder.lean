module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

@[expose] public section

/-! Exact exponential comparison with a factorial remainder. The primitive
is explicit, so no differentiability of the compared function is needed. -/
noncomputable section
open MeasureTheory Set
namespace FourPapersCommon
set_option maxHeartbeats 500000

theorem exponentialVolterraRemainder_integral (A B K t : ℝ) (n : ℕ) :
    A+K*(∫s in (0 : ℝ)..t,A*Real.exp (K*s)+B*(K*s)^n/(n.factorial : ℝ))=
      A*Real.exp (K*t)+B*(K*t)^(n+1)/((n+1).factorial : ℝ) := by
  let G := fun s : ℝ=>A*Real.exp (K*s)+B*(K*s)^(n+1)/((n+1).factorial : ℝ)
  have hN : ((n+1).factorial : ℝ)≠0 := by positivity
  have hn : (n.factorial : ℝ)≠0 := by positivity
  have hG (s : ℝ) : HasDerivAt G
      (K*(A*Real.exp (K*s)+B*(K*s)^n/(n.factorial : ℝ))) s := by
    have h := ((((hasDerivAt_id s).const_mul K).exp.const_mul A).add
      ((((hasDerivAt_id s).const_mul K).pow (n+1)).const_mul B |>.div_const
        ((n+1).factorial : ℝ)))
    convert h using 1
    · rfl
    · simp only [id_eq,Nat.add_sub_cancel,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      field_simp <;> ring
  have hI : (∫s in (0 : ℝ)..t,K*(A*Real.exp (K*s)+B*(K*s)^n/(n.factorial : ℝ)))=
      G t-G 0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _=>hG s) ((by fun_prop : Continuous (fun s : ℝ=>
          K*(A*Real.exp (K*s)+B*(K*s)^n/(n.factorial : ℝ)))).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul] at hI
  have hzero : G 0=A := by simp [G]
  rw [hzero] at hI
  dsimp only [G] at hI
  linarith

end FourPapersCommon
