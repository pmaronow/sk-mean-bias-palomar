module
public import QuantitativePaper.CommonExponentialJetEnvelope

@[expose] public section

/-! A genuine common envelope for finitely many selected derivative
orders, obtained from their separately proved exponential bounds. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 800000
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_common_finite_exponential_jet_bound (N : ℕ) (f : E→ℝ) (U : Set E)
    (h : ∀r : ℕ,r≤N→∃C R : ℝ,0≤C ∧ 0≤R ∧ ∀x∈U,
      ‖iteratedFDeriv ℝ r f x‖≤C*Real.exp (R*‖x‖)) :
    ∃C R : ℝ,1≤C ∧ 0≤R ∧ ∀r : ℕ,r≤N→∀x∈U,
      ‖iteratedFDeriv ℝ r f x‖≤C*Real.exp (R*‖x‖) := by
  classical
  have hh (i : Fin (N+1)):=h i.1 (Nat.le_of_lt_succ i.2)
  choose C R hC hR hBounds using hh
  let C':=1+∑i : Fin (N+1),C i
  let R':=∑i : Fin (N+1),R i
  have hCs : 0≤∑i : Fin (N+1),C i:=Finset.sum_nonneg fun i _=>hC i
  refine ⟨C',R',by dsimp [C'];linarith,Finset.sum_nonneg (fun i _=>hR i),?_⟩
  intro r hr x hx
  let i : Fin (N+1):=⟨r,by omega⟩
  have hc : C i≤C':=by
    have hh:=Finset.single_le_sum (fun j _=>hC j) (Finset.mem_univ i)
    dsimp [C']
    linarith
  have hrate : R i≤R':=Finset.single_le_sum (fun j _=>hR j) (Finset.mem_univ i)
  exact (hBounds i x hx).trans (mul_le_mul hc
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrate (norm_nonneg x)))
      (Real.exp_pos _).le (by dsimp [C'];linarith))

end QuantitativePaper
