module
public import FourPapersCommon.FiniteStreamingPolynomialsBudget

@[expose] public section

/-! All repeated within derivatives and uniform bounds follow from a genuine
finite streaming identity and its one-step cost/weight estimates. -/
noncomputable section
namespace FourPapersCommon.FiniteStreamingPolynomials
variable {A : Type*}

def iterate (R : A → Polynomial A) (P : Polynomial A) : ℕ → Polynomial A
  | 0 => P
  | r + 1 => derivative R (iterate R P r)

def withinJet (g : ℝ → ℝ) (S : Set ℝ) : ℕ → ℝ → ℝ
  | 0 => g
  | r + 1 => derivWithin (withinJet g S r) S

def growth (K : ℝ) (C : ℕ) : ℕ → ℝ
  | 0 => 1
  | r + 1 => K * (C + 2 * r : ℕ)^2 * growth K C r

theorem growth_nonneg (K : ℝ) (hK : 0 ≤ K) (C r : ℕ) : 0 ≤ growth K C r := by
  induction r with
  | zero => simp [growth]
  | succ r ih => exact mul_nonneg (mul_nonneg hK (sq_nonneg _)) ih

theorem costBound_iterate (R : A → Polynomial A) (c : A → ℕ)
    (hR : ∀ a, costBound c (c a + 2) (R a)) (C : ℕ) (P : Polynomial A)
    (hP : costBound c C P) (r : ℕ) : costBound c (C + 2 * r) (iterate R P r) := by
  induction r with
  | zero => simpa [iterate] using hP
  | succ r ih =>
    simpa only [iterate, Nat.mul_succ, Nat.add_assoc] using
      costBound_derivative R c hR (C + 2 * r) (iterate R P r) ih

theorem budget_iterate_le (R : A → Polynomial A) (B : A → ℝ)
    (hB : ∀ a, 0 ≤ B a) (c : A → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hRc : ∀ a, costBound c (c a + 2) (R a))
    (hRB : ∀ a, budget B (R a) ≤ K * (c a : ℝ)^2 * B a)
    (C : ℕ) (P : Polynomial A) (hP : costBound c C P) (r : ℕ) :
    budget B (iterate R P r) ≤ growth K C r * budget B P := by
  induction r with
  | zero => simp [iterate, growth]
  | succ r ih =>
    change budget B (derivative R (iterate R P r)) ≤
      (K * (C + 2 * r : ℕ)^2 * growth K C r) * budget B P
    calc
      _ ≤ K * (C + 2 * r : ℕ)^2 * budget B (iterate R P r) :=
        budget_derivative_le R B hB c K hK hRB _ _ (costBound_iterate R c hRc C P hP r)
      _ ≤ K * (C + 2 * r : ℕ)^2 * (growth K C r * budget B P) :=
        mul_le_mul_of_nonneg_left ih (mul_nonneg hK (sq_nonneg _))
      _ = _ := by ring

theorem withinJet_eq_eval_iterate (f : A → ℝ → ℝ) (R : A → Polynomial A)
    (S : Set ℝ) (hS : UniqueDiffOn ℝ S)
    (hR : ∀ a u, u ∈ S → HasDerivWithinAt (f a) (eval f (R a) u) S u)
    (P : Polynomial A) (r : ℕ) :
    Set.EqOn (withinJet (fun x => eval f P x) S r) (eval f (iterate R P r)) S := by
  induction r with
  | zero => intro u hu; rfl
  | succ r ih =>
    intro u hu
    change derivWithin (withinJet (fun x => eval f P x) S r) S u =
      eval f (derivative R (iterate R P r)) u
    rw [derivWithin_congr ih (ih hu)]
    exact (hasDerivWithinAt_eval f R S u (fun a => hR a u hu) _).derivWithin (hS u hu)

theorem hasDerivWithinAt_withinJet (f : A → ℝ → ℝ) (R : A → Polynomial A)
    (S : Set ℝ) (hS : UniqueDiffOn ℝ S)
    (hR : ∀ a u, u ∈ S → HasDerivWithinAt (f a) (eval f (R a) u) S u)
    (P : Polynomial A) (r : ℕ) (u : ℝ) (hu : u ∈ S) :
    HasDerivWithinAt (withinJet (fun x => eval f P x) S r)
      (withinJet (fun x => eval f P x) S (r + 1) u) S u := by
  have hi := withinJet_eq_eval_iterate f R S hS hR P r
  have hi' := withinJet_eq_eval_iterate f R S hS hR P (r + 1)
  rw [hi' hu]
  exact (hasDerivWithinAt_eval f R S u (fun a => hR a u hu) (iterate R P r)).congr
    (fun x hx => hi hx) (hi hu)

theorem abs_withinJet_le (f : A → ℝ → ℝ) (R : A → Polynomial A)
    (S : Set ℝ) (hS : UniqueDiffOn ℝ S)
    (hR : ∀ a u, u ∈ S → HasDerivWithinAt (f a) (eval f (R a) u) S u)
    (B : A → ℝ) (hB : ∀ a, 0 ≤ B a)
    (hf : ∀ a u, u ∈ S → |f a u| ≤ B a)
    (c : A → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hRc : ∀ a, costBound c (c a + 2) (R a))
    (hRB : ∀ a, budget B (R a) ≤ K * (c a : ℝ)^2 * B a)
    (C : ℕ) (P : Polynomial A) (hP : costBound c C P)
    (r : ℕ) (u : ℝ) (hu : u ∈ S) :
    |withinJet (fun x => eval f P x) S r u| ≤ growth K C r * budget B P := by
  rw [withinJet_eq_eval_iterate f R S hS hR P r hu]
  exact (abs_eval_le_budget f B u (fun a => hf a u hu) _).trans
    (budget_iterate_le R B hB c K hK hRc hRB C P hP r)

end FourPapersCommon.FiniteStreamingPolynomials
