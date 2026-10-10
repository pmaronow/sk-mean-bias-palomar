module
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Tactic

@[expose] public section

/-! Finite streaming expressions as actual polynomials of physical atoms.
The response is an explicit finite polynomial.  Only its first derivative
identity is an input; repeated derivatives are obtained by the product rule. -/
noncomputable section
namespace FourPapersCommon.FiniteStreamingPolynomials

abbrev Monomial (A : Type*) := List A
abbrev Polynomial (A : Type*) := List (ℝ × Monomial A)

def monoEval {A : Type*} (f : A → ℝ → ℝ) (l : Monomial A) (u : ℝ) : ℝ :=
  (l.map fun a => f a u).prod

def eval {A : Type*} (f : A → ℝ → ℝ) (P : Polynomial A) (u : ℝ) : ℝ :=
  (P.map fun t => t.1 * monoEval f t.2 u).sum

def scale {A : Type*} (c : ℝ) (P : Polynomial A) : Polynomial A :=
  P.map fun t => (c * t.1, t.2)

def suffix {A : Type*} (P : Polynomial A) (l : Monomial A) : Polynomial A :=
  P.map fun t => (t.1, t.2 ++ l)

def prepend {A : Type*} (a : A) (P : Polynomial A) : Polynomial A :=
  P.map fun t => (t.1, a :: t.2)

def monoDerivative {A : Type*} (R : A → Polynomial A) : Monomial A → Polynomial A
  | [] => []
  | a :: l => suffix (R a) l ++ prepend a (monoDerivative R l)

def derivative {A : Type*} (R : A → Polynomial A) (P : Polynomial A) : Polynomial A :=
  P.flatMap fun t => scale t.1 (monoDerivative R t.2)

@[simp] theorem monoEval_nil {A : Type*} (f : A → ℝ → ℝ) (u : ℝ) :
    monoEval f [] u = 1 := rfl

@[simp] theorem monoEval_cons {A : Type*} (f : A → ℝ → ℝ) (a : A)
    (l : Monomial A) (u : ℝ) :
    monoEval f (a :: l) u = f a u * monoEval f l u := rfl

theorem monoEval_append {A : Type*} (f : A → ℝ → ℝ) (l m : Monomial A) (u : ℝ) :
    monoEval f (l ++ m) u = monoEval f l u * monoEval f m u := by
  simp [monoEval, List.map_append, List.prod_append]

@[simp] theorem eval_nil {A : Type*} (f : A → ℝ → ℝ) (u : ℝ) : eval f [] u = 0 := rfl

@[simp] theorem eval_cons {A : Type*} (f : A → ℝ → ℝ) (t : ℝ × Monomial A)
    (P : Polynomial A) (u : ℝ) :
    eval f (t :: P) u = t.1 * monoEval f t.2 u + eval f P u := rfl

theorem eval_append {A : Type*} (f : A → ℝ → ℝ) (P Q : Polynomial A) (u : ℝ) :
    eval f (P ++ Q) u = eval f P u + eval f Q u := by
  simp [eval, List.map_append, List.sum_append]

theorem eval_scale {A : Type*} (f : A → ℝ → ℝ) (c : ℝ)
    (P : Polynomial A) (u : ℝ) : eval f (scale c P) u = c * eval f P u := by
  induction P with
  | nil => simp [scale]
  | cons t P ih => simp only [scale, List.map_cons, eval_cons] at *; rw [ih]; ring

theorem eval_suffix {A : Type*} (f : A → ℝ → ℝ) (P : Polynomial A)
    (l : Monomial A) (u : ℝ) :
    eval f (suffix P l) u = eval f P u * monoEval f l u := by
  induction P with
  | nil => simp [suffix]
  | cons t P ih =>
    simp only [suffix, List.map_cons, eval_cons, monoEval_append] at *
    rw [ih]; ring

theorem eval_prepend {A : Type*} (f : A → ℝ → ℝ) (a : A)
    (P : Polynomial A) (u : ℝ) : eval f (prepend a P) u = f a u * eval f P u := by
  induction P with
  | nil => simp [prepend]
  | cons t P ih =>
    simp only [prepend, List.map_cons, eval_cons, monoEval_cons] at *
    rw [ih]; ring

theorem eval_monoDerivative_cons {A : Type*} (f : A → ℝ → ℝ)
    (R : A → Polynomial A) (a : A) (l : Monomial A) (u : ℝ) :
    eval f (monoDerivative R (a :: l)) u =
      eval f (R a) u * monoEval f l u + f a u * eval f (monoDerivative R l) u := by
  rw [monoDerivative, eval_append, eval_suffix, eval_prepend]

theorem eval_derivative_cons {A : Type*} (f : A → ℝ → ℝ)
    (R : A → Polynomial A) (t : ℝ × Monomial A) (P : Polynomial A) (u : ℝ) :
    eval f (derivative R (t :: P)) u =
      t.1 * eval f (monoDerivative R t.2) u + eval f (derivative R P) u := by
  simp only [derivative, List.flatMap_cons, eval_append, eval_scale]

theorem hasDerivWithinAt_monoEval {A : Type*} (f : A → ℝ → ℝ)
    (R : A → Polynomial A) (S : Set ℝ) (u : ℝ)
    (hR : ∀ a, HasDerivWithinAt (f a) (eval f (R a) u) S u)
    (l : Monomial A) :
    HasDerivWithinAt (fun x => monoEval f l x) (eval f (monoDerivative R l) u) S u := by
  induction l with
  | nil => simpa [monoDerivative] using hasDerivWithinAt_const u S (1 : ℝ)
  | cons a l ih =>
    simpa only [monoEval_cons, eval_monoDerivative_cons] using (hR a).fun_mul ih

theorem hasDerivWithinAt_eval {A : Type*} (f : A → ℝ → ℝ)
    (R : A → Polynomial A) (S : Set ℝ) (u : ℝ)
    (hR : ∀ a, HasDerivWithinAt (f a) (eval f (R a) u) S u)
    (P : Polynomial A) :
    HasDerivWithinAt (fun x => eval f P x) (eval f (derivative R P) u) S u := by
  induction P with
  | nil => simpa [derivative] using hasDerivWithinAt_const u S (0 : ℝ)
  | cons t P ih =>
    have ht := (hasDerivWithinAt_monoEval f R S u hR t.2).const_mul t.1
    simpa only [eval_cons, eval_derivative_cons] using ht.fun_add ih

end FourPapersCommon.FiniteStreamingPolynomials
