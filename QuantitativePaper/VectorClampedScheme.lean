module
public import QuantitativePaper.VectorDyadicRefinement

@[expose] public section

/-! An actual finite scheme representing a vector recursion restarted at
overlap q. A dummy zero-mass root interval retains admissibility; its Gaussian
step is omitted in the tail value. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

def clampedSchemeMass {k : ℕ} (s : RSBScheme k) (i : ℕ) : ℝ :=
  if i=0 then 0 else s.m (i-1)

def clampedSchemeOverlap {k : ℕ} (s : RSBScheme k) (q : ℝ) (i : ℕ) : ℝ :=
  if i=0 then 0 else max q (s.q (i-1))

def vectorClampedScheme {k : ℕ} (s : RSBScheme k) (q : ℝ) (hq : q∈Icc (0 : ℝ) 1) :
    RSBScheme (k+1) where
  m := clampedSchemeMass s
  q := clampedSchemeOverlap s q
  m_zero := by simp [clampedSchemeMass]
  m_top := by simp [clampedSchemeMass,s.m_top]
  m_mono i hi := by
    by_cases h0 : i=0
    · subst i
      simp [clampedSchemeMass,s.m_zero]
    · simp only [clampedSchemeMass,ite_eq_right h0,ite_eq_right (by omega : i+1≠0),Nat.add_sub_cancel]
      exact s.m_mono' i hi (i-1) (by omega)
  q_zero := by simp [clampedSchemeOverlap]
  q_top := by simp [clampedSchemeOverlap,s.q_top,max_eq_right hq.2]
  q_mono i hi := by
    by_cases h0 : i=0
    · subst i
      simp [clampedSchemeOverlap,s.q_zero,max_eq_left hq.1]
      exact hq.1
    · simp only [clampedSchemeOverlap,ite_eq_right h0,ite_eq_right (by omega : i+1≠0),Nat.add_sub_cancel]
      exact max_le_max le_rfl (s.q_mono' i hi (i-1) (by omega))

@[simp] theorem vectorClampedScheme_mass_succ {k : ℕ} (s : RSBScheme k) (q : ℝ)
    (hq : q∈Icc (0 : ℝ) 1) (i : ℕ) :
    (vectorClampedScheme s q hq).m (i+1)=s.m i := by
  simp [vectorClampedScheme,clampedSchemeMass]

@[simp] theorem vectorClampedScheme_overlap_succ {k : ℕ} (s : RSBScheme k) (q : ℝ)
    (hq : q∈Icc (0 : ℝ) 1) (i : ℕ) :
    (vectorClampedScheme s q hq).q (i+1)=max q (s.q i) := by
  simp [vectorClampedScheme,clampedSchemeOverlap]

def vectorTailRecursion {n k : ℕ} (s : RSBScheme k) (β t q : ℝ) (p : Couplings n×ℝ) :
    ℕ→(Field n→ℝ)
  | 0 => vectorTerminalPotential n β t p
  | j+1 => vectorColeHopfStep ((1-t)*(β^2*(max q (s.q (k+2-j))-max q (s.q (k+1-j)))))
      (s.m (k+1-j)) (vectorTailRecursion s β t q p j)

theorem vectorTailRecursion_eq_clamped {n k : ℕ} (s : RSBScheme k) (β t q : ℝ)
    (hq : q∈Icc (0 : ℝ) 1) (p : Couplings n×ℝ) {j : ℕ} (hj : j ≤ k+2) :
    vectorTailRecursion s β t q p j=vectorRecursion (vectorClampedScheme s q hq) β t p j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [vectorTailRecursion,vectorRecursion,ih (by omega)]
    have hi : k+1+1-j=(k+1-j)+1 := by omega
    have hi' : k+1+2-j=(k+2-j)+1 := by omega
    rw [hi,hi',vectorClampedScheme_mass_succ,vectorClampedScheme_overlap_succ,
      vectorClampedScheme_overlap_succ]
    simp only [show k+1-j+1=k+2-j by omega]

theorem vectorTailRecursion_zero {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) {j : ℕ} (hj : j ≤ k+2) :
    vectorTailRecursion s β t 0 p j=vectorRecursion s β t p j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [vectorTailRecursion,vectorRecursion,ih (by omega),
      max_eq_right (s.q_nonneg (by omega : k+2-j ≤ k+2)),
      max_eq_right (s.q_nonneg (by omega : k+1-j ≤ k+2))]

theorem vectorTailRecursion_one {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) {j : ℕ} (hj : j ≤ k+2) :
    vectorTailRecursion s β t 1 p j=vectorTerminalPotential n β t p := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext x
    rw [vectorTailRecursion,ih (by omega),
      max_eq_left (s.q_le_one (by omega : k+2-j ≤ k+2)),
      max_eq_left (s.q_le_one (by omega : k+1-j ≤ k+2))]
    simp

end QuantitativePaper
