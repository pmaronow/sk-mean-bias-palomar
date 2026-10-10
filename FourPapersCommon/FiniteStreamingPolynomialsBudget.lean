module
public import FourPapersCommon.FiniteStreamingPolynomials

@[expose] public section

/-! Explicit cost and absolute coefficient budgets for streaming polynomials.
These estimates are proved from atom sup bounds and the concrete response list. -/
noncomputable section
namespace FourPapersCommon.FiniteStreamingPolynomials
variable {A : Type*}

def monoWeight (B : A → ℝ) (l : Monomial A) : ℝ := (l.map B).prod
def monoCost (c : A → ℕ) (l : Monomial A) : ℕ := (l.map c).sum
def budget (B : A → ℝ) (P : Polynomial A) : ℝ :=
  (P.map fun t => |t.1| * monoWeight B t.2).sum
def costBound (c : A → ℕ) (C : ℕ) (P : Polynomial A) : Prop :=
  ∀ t ∈ P, monoCost c t.2 ≤ C

@[simp] theorem monoWeight_nil (B : A → ℝ) : monoWeight B [] = 1 := rfl
@[simp] theorem monoWeight_cons (B : A → ℝ) (a : A) (l : Monomial A) :
    monoWeight B (a :: l) = B a * monoWeight B l := rfl
@[simp] theorem monoCost_nil (c : A → ℕ) : monoCost c [] = 0 := rfl
@[simp] theorem monoCost_cons (c : A → ℕ) (a : A) (l : Monomial A) :
    monoCost c (a :: l) = c a + monoCost c l := rfl
theorem monoWeight_append (B : A → ℝ) (l m : Monomial A) :
    monoWeight B (l ++ m) = monoWeight B l * monoWeight B m := by
  simp [monoWeight, List.map_append, List.prod_append]
theorem monoCost_append (c : A → ℕ) (l m : Monomial A) :
    monoCost c (l ++ m) = monoCost c l + monoCost c m := by
  simp [monoCost, List.map_append, List.sum_append]
@[simp] theorem budget_nil (B : A → ℝ) : budget B [] = 0 := rfl
@[simp] theorem budget_cons (B : A → ℝ) (t : ℝ × Monomial A) (P : Polynomial A) :
    budget B (t :: P) = |t.1| * monoWeight B t.2 + budget B P := rfl
theorem budget_append (B : A → ℝ) (P Q : Polynomial A) :
    budget B (P ++ Q) = budget B P + budget B Q := by
  simp [budget, List.map_append, List.sum_append]
theorem budget_scale (B : A → ℝ) (k : ℝ) (P : Polynomial A) :
    budget B (scale k P) = |k| * budget B P := by
  induction P with
  | nil => simp [scale]
  | cons t P ih =>
    simp only [scale, List.map_cons, budget_cons, abs_mul] at *
    rw [ih]; ring
theorem budget_suffix (B : A → ℝ) (P : Polynomial A) (l : Monomial A) :
    budget B (suffix P l) = budget B P * monoWeight B l := by
  induction P with
  | nil => simp [suffix]
  | cons t P ih =>
    simp only [suffix, List.map_cons, budget_cons, monoWeight_append] at *
    rw [ih]; ring
theorem budget_prepend (B : A → ℝ) (a : A) (P : Polynomial A) :
    budget B (prepend a P) = B a * budget B P := by
  induction P with
  | nil => simp [prepend]
  | cons t P ih =>
    simp only [prepend, List.map_cons, budget_cons, monoWeight_cons] at *
    rw [ih]; ring
theorem monoWeight_nonneg (B : A → ℝ) (hB : ∀ a, 0 ≤ B a) (l : Monomial A) :
    0 ≤ monoWeight B l := by
  induction l with
  | nil => simp
  | cons a l ih => exact mul_nonneg (hB a) ih
theorem budget_nonneg (B : A → ℝ) (hB : ∀ a, 0 ≤ B a) (P : Polynomial A) :
    0 ≤ budget B P := by
  induction P with
  | nil => simp
  | cons t P ih => exact add_nonneg (mul_nonneg (abs_nonneg _) (monoWeight_nonneg B hB _)) ih

theorem abs_monoEval_le (f : A → ℝ → ℝ) (B : A → ℝ) (u : ℝ)
    (hf : ∀ a, |f a u| ≤ B a) (l : Monomial A) :
    |monoEval f l u| ≤ monoWeight B l := by
  have hB a : 0 ≤ B a := le_trans (abs_nonneg _) (hf a)
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [monoEval_cons, monoWeight_cons, abs_mul]
    exact mul_le_mul (hf a) ih (abs_nonneg _) (hB a)

theorem abs_eval_le_budget (f : A → ℝ → ℝ) (B : A → ℝ) (u : ℝ)
    (hf : ∀ a, |f a u| ≤ B a) (P : Polynomial A) : |eval f P u| ≤ budget B P := by
  induction P with
  | nil => simp
  | cons t P ih =>
    rw [eval_cons, budget_cons]
    apply (abs_add_le _ _).trans
    apply add_le_add _ ih
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_monoEval_le f B u hf t.2) (abs_nonneg _)

theorem costBound_monoDerivative (R : A → Polynomial A) (c : A → ℕ)
    (hR : ∀ a, costBound c (c a + 2) (R a)) (l : Monomial A) :
    costBound c (monoCost c l + 2) (monoDerivative R l) := by
  induction l with
  | nil => simp [monoDerivative, costBound]
  | cons a l ih =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_map.mp ht with ⟨v, hv, rfl⟩
      have hh := hR a v hv
      simp only [monoCost_append, monoCost_cons]
      omega
    · rcases List.mem_map.mp ht with ⟨v, hv, rfl⟩
      have hh := ih v hv
      simp only [monoCost_cons]
      omega

theorem costBound_derivative (R : A → Polynomial A) (c : A → ℕ)
    (hR : ∀ a, costBound c (c a + 2) (R a)) (C : ℕ) (P : Polynomial A)
    (hP : costBound c C P) : costBound c (C + 2) (derivative R P) := by
  intro t ht
  rcases List.mem_flatMap.mp ht with ⟨v, hv, ht⟩
  rcases List.mem_map.mp ht with ⟨w, hw, rfl⟩
  have hh := costBound_monoDerivative R c hR v.2 w hw
  have hp := hP v hv
  exact hh.trans (Nat.add_le_add_right hp 2)

theorem budget_monoDerivative_le (R : A → Polynomial A) (B : A → ℝ)
    (hB : ∀ a, 0 ≤ B a) (c : A → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hR : ∀ a, budget B (R a) ≤ K * (c a : ℝ)^2 * B a) (l : Monomial A) :
    budget B (monoDerivative R l) ≤ K * (monoCost c l : ℝ)^2 * monoWeight B l := by
  induction l with
  | nil => simp [monoDerivative]
  | cons a l ih =>
    rw [monoDerivative, budget_append, budget_suffix, budget_prepend, monoWeight_cons,
      monoCost_cons, Nat.cast_add]
    have hm := monoWeight_nonneg B hB l
    calc
      budget B (R a) * monoWeight B l + B a * budget B (monoDerivative R l)
        ≤ (K * (c a : ℝ)^2 * B a) * monoWeight B l +
            B a * (K * (monoCost c l : ℝ)^2 * monoWeight B l) :=
        add_le_add (mul_le_mul_of_nonneg_right (hR a) hm)
          (mul_le_mul_of_nonneg_left ih (hB a))
      _ = K * ((c a : ℝ)^2 + (monoCost c l : ℝ)^2) *
          (B a * monoWeight B l) := by ring
      _ ≤ K * ((c a : ℝ) + (monoCost c l : ℝ))^2 *
          (B a * monoWeight B l) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (hB a) hm)
        apply mul_le_mul_of_nonneg_left _ hK
        have hca : (0 : ℝ) ≤ c a := Nat.cast_nonneg _
        have hcl : (0 : ℝ) ≤ monoCost c l := Nat.cast_nonneg _
        nlinarith

theorem budget_derivative_le (R : A → Polynomial A) (B : A → ℝ)
    (hB : ∀ a, 0 ≤ B a) (c : A → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hR : ∀ a, budget B (R a) ≤ K * (c a : ℝ)^2 * B a)
    (C : ℕ) (P : Polynomial A) (hP : costBound c C P) :
    budget B (derivative R P) ≤ K * (C : ℝ)^2 * budget B P := by
  induction P with
  | nil => simp [derivative]
  | cons t P ih =>
    have ht := hP t (by simp)
    have hp : costBound c C P := fun v hv => hP v (by simp [hv])
    rw [derivative, List.flatMap_cons, budget_append, budget_scale, budget_cons]
    have hm := monoWeight_nonneg B hB t.2
    have hc : (monoCost c t.2 : ℝ)^2 ≤ (C : ℝ)^2 := by
      exact sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _) |>.2 (by exact_mod_cast ht)
    calc
      |t.1| * budget B (monoDerivative R t.2) + budget B (derivative R P)
        ≤ |t.1| * (K * (monoCost c t.2 : ℝ)^2 * monoWeight B t.2) +
            K * (C : ℝ)^2 * budget B P :=
          add_le_add (mul_le_mul_of_nonneg_left
            (budget_monoDerivative_le R B hB c K hK hR t.2) (abs_nonneg _)) (ih hp)
      _ ≤ |t.1| * (K * (C : ℝ)^2 * monoWeight B t.2) +
            K * (C : ℝ)^2 * budget B P := by
          apply add_le_add _ le_rfl
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hK) hm) (abs_nonneg _)
      _ = K * (C : ℝ)^2 * (|t.1| * monoWeight B t.2 + budget B P) := by ring

end FourPapersCommon.FiniteStreamingPolynomials
