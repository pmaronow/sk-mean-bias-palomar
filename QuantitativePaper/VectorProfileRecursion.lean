module
public import QuantitativePaper.VectorSmooth
public import QuantitativePaper.VectorClampedScheme

@[expose] public section

/-! Literal affine-profile recursion. Its real parameter extension agrees
with the genuine convex finite Parisi scheme throughout the physical unit
interval, including zero masses and clamped overlap nodes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 800000

def vectorProfileMass {k : ℕ} (s₀ s₁ : RSBScheme k) (θ : ℝ) (i : ℕ) : ℝ :=
  (1-θ)*s₀.m i+θ*s₁.m i

def vectorProfileScheme {k : ℕ} (s₀ s₁ : RSBScheme k) (θ : ℝ)
    (hθ : θ ∈ Icc (0:ℝ) 1) : RSBScheme k where
  m := vectorProfileMass s₀ s₁ θ
  q := s₀.q
  m_zero := by simp only [vectorProfileMass, s₀.m_zero, s₁.m_zero, mul_zero, add_zero]
  m_top := by simp only [vectorProfileMass, s₀.m_top, s₁.m_top, mul_one]; ring
  m_mono i hi := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left (s₀.m_mono i hi) (sub_nonneg.mpr hθ.2))
      (mul_le_mul_of_nonneg_left (s₁.m_mono i hi) hθ.1)
  q_zero := s₀.q_zero
  q_top := s₀.q_top
  q_mono := s₀.q_mono

def vectorProfileRecursion {n k : ℕ} (s₀ s₁ : RSBScheme k) (β t θ : ℝ)
    (p : Couplings n × ℝ) : ℕ → Field n → ℝ
  | 0 => vectorTerminalPotential n β t p
  | j+1 => vectorColeHopfStep ((1-t)*(β^2*(s₀.q (k+2-j)-s₀.q (k+1-j))))
      (vectorProfileMass s₀ s₁ θ (k+1-j)) (vectorProfileRecursion s₀ s₁ β t θ p j)

def vectorProfileTailRecursion {n k : ℕ} (s₀ s₁ : RSBScheme k) (β t q θ : ℝ)
    (p : Couplings n × ℝ) : ℕ → Field n → ℝ
  | 0 => vectorTerminalPotential n β t p
  | j+1 => vectorColeHopfStep ((1-t)*(β^2*(max q (s₀.q (k+2-j))-max q (s₀.q (k+1-j)))))
      (vectorProfileMass s₀ s₁ θ (k+1-j)) (vectorProfileTailRecursion s₀ s₁ β t q θ p j)

theorem vectorProfileRecursion_eq_scheme {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) (p : Couplings n × ℝ) (j : ℕ) :
    vectorProfileRecursion s₀ s₁ β t θ p j=
      vectorRecursion (vectorProfileScheme s₀ s₁ θ hθ) β t p j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [vectorProfileRecursion, vectorRecursion, ih]
    rfl

theorem vectorProfileTailRecursion_eq_scheme {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (β t q θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) (p : Couplings n × ℝ) (j : ℕ) :
    vectorProfileTailRecursion s₀ s₁ β t q θ p j=
      vectorTailRecursion (vectorProfileScheme s₀ s₁ θ hθ) β t q p j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [vectorProfileTailRecursion, vectorTailRecursion, ih]
    rfl

theorem vectorProfileRecursion_zero {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) :
    vectorProfileRecursion s₀ s₁ β t 0 p j=vectorRecursion s₀ β t p j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [vectorProfileRecursion, vectorRecursion, vectorProfileMass,
      sub_zero, one_mul, zero_mul, add_zero, ih]

theorem vectorProfileRecursion_one {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (hq : s₀.q=s₁.q) (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) :
    vectorProfileRecursion s₀ s₁ β t 1 p j=vectorRecursion s₁ β t p j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [vectorProfileRecursion, vectorRecursion, vectorProfileMass,
      sub_self, zero_mul, one_mul, zero_add, ih, hq]

theorem vectorProfileMass_zero_or_pos {k : ℕ} (s₀ s₁ : RSBScheme k)
    (i : ℕ) (hi : i ≤ k+1) :
    (∀ θ, vectorProfileMass s₀ s₁ θ i=0) ∨
      (∀ θ ∈ Ioo (0:ℝ) 1, 0 < vectorProfileMass s₀ s₁ θ i) := by
  by_cases h₀ : s₀.m i=0
  · by_cases h₁ : s₁.m i=0
    · exact Or.inl (fun θ => by simp only [vectorProfileMass, h₀, h₁, mul_zero, add_zero])
    · right
      intro θ hθ
      have hp : 0 < s₁.m i := lt_of_le_of_ne (s₁.m_nonneg hi) (Ne.symm h₁)
      simpa only [vectorProfileMass, h₀, mul_zero, zero_add] using mul_pos hθ.1 hp
  · right
    intro θ hθ
    have hp : 0 < s₀.m i := lt_of_le_of_ne (s₀.m_nonneg hi) (Ne.symm h₀)
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hθ.2) hp)
      (mul_nonneg hθ.1.le (s₁.m_nonneg hi))

theorem vectorProfileRecursion_lipschitz {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) (p : Couplings n × ℝ) (j : ℕ) :
    LipschitzWith (Real.sqrt (n:ℝ)).toNNReal (vectorProfileRecursion s₀ s₁ β t θ p j) := by
  rw [vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ]
  exact vectorRecursion_lipschitz _ β t p j

theorem vectorProfileRecursion_terminal_joint_smooth {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (β t : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × VectorParameter n => vectorProfileRecursion s₀ s₁ β t z.1 z.2.1 0 z.2.2) := by
  apply contDiff_infty.mpr
  intro N
  exact (contDiff_vectorTerminalPotential_joint n β t N).comp contDiff_snd

end QuantitativePaper
