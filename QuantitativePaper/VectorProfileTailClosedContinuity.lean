module
public import QuantitativePaper.VectorProfileTailCellContinuity
public import QuantitativePaper.VectorProfileTailCellJetBounds

@[expose] public section

/-! Literal closed-cell continuity and envelopes of the actual restarted
tail recursion. All profile and field jets are genuine derivatives. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem continuousOn_vectorProfileTailRecursion_retained_jets (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (i : ℕ) (hi : i ≤ k+1) (r : ℕ) :
    ContinuousOn (fun w : ℝ×(ℝ×VectorParameter n) =>
      iteratedFDeriv ℝ r (fun y => vectorProfileTailRecursion s₀ s₁ β t w.1 y.1 y.2.1 (k+2) y.2.2) w.2)
      (Icc (s₀.q i) (s₀.q (i+1)) ×ˢ {y : ℝ×VectorParameter n | y.1 ∈ Ioo (0:ℝ) 1}) := by
  have hC : ContinuousOn (fun w : ℝ×(ℝ×VectorParameter n) =>
      iteratedFDeriv ℝ r (fun y => vectorProfilePhysicalCell s₀ s₁ β t i (w.1,y)) w.2)
      (Icc (s₀.q i) (s₀.q (i+1)) ×ˢ {y : ℝ×VectorParameter n | y.1 ∈ Ioo (0:ℝ) 1}) :=
    (continuousOn_retained_iteratedFDeriv_vectorProfileCellFunction (n:=n) s₀ s₁ β t ht
      ((1-t)*β^2) (s₀.q (i+1)) i (k+1-i) hi r).mono (fun _ h => h.2)
  apply hC.congr
  intro w hw
  exact (vectorProfileCellFunction_retained_jet_eq_tail s₀ s₁ β t i hi w.1 hw.1 w.2 hw.2 r).symm

theorem exists_vectorProfileTailRecursion_closed_retained_exp_jets (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (i N : ℕ) (hi : i ≤ k+1)
    (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C R : ℝ, 1 ≤ C ∧ 0 ≤ R ∧ ∀ r, r ≤ N →
      ∀ q ∈ Icc (s₀.q i) (s₀.q (i+1)), ∀ y : ℝ×VectorParameter n, y.1 ∈ Ioo a b →
      ‖iteratedFDeriv ℝ r (fun z => vectorProfileTailRecursion s₀ s₁ β t q z.1 z.2.1 (k+2) z.2.2) y‖ ≤
        C*Real.exp (R*‖y‖) := by
  obtain ⟨C,R,hC,hR,hjets⟩ := exists_vectorProfileCellFunction_closed_retained_exp_jets
    (n:=n) s₀ s₁ β t ht ((1-t)*β^2) (s₀.q (i+1)) (s₀.q i) (s₀.q (i+1)) a b
    (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β)) ha hb i (k+1-i) N hi
  refine ⟨C,R,hC,hR,?_⟩
  intro r hr q hq y hy
  have hθ : y.1 ∈ Ioo (0:ℝ) 1 := ⟨ha.trans hy.1,hy.2.trans hb⟩
  rw [←vectorProfileCellFunction_retained_jet_eq_tail s₀ s₁ β t i hi q hq y hθ r]
  exact hjets r hr q hq y hy

end QuantitativePaper
