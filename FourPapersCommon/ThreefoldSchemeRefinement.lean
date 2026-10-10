module
public import FourPapersCommon.MixedScheme

@[expose] public section

/-! Three-way same-mass refinements of genuine finite overlap probability
measures. The inserted nodes are arbitrary ordered points in the original
cells; no minimizer or covariance assumption is needed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace FourPapersCommon
open SpinGlass.Targets
set_option maxHeartbeats 1200000

def threefoldNode {k : ℕ} (s : RSBScheme k) (a b : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j % 3 = 0 then s.q (j / 3) else if j % 3 = 1 then a (j / 3) else b (j / 3)

theorem threefoldNode_zero {k : ℕ} (s : RSBScheme k) (a b : ℕ → ℝ) (i : ℕ) :
    threefoldNode s a b (3*i) = s.q i := by simp [threefoldNode, Nat.mul_comm]
theorem threefoldNode_one {k : ℕ} (s : RSBScheme k) (a b : ℕ → ℝ) (i : ℕ) :
    threefoldNode s a b (3*i+1) = a i := by simp [threefoldNode, Nat.mul_comm, Nat.add_div]
theorem threefoldNode_two {k : ℕ} (s : RSBScheme k) (a b : ℕ → ℝ) (i : ℕ) :
    threefoldNode s a b (3*i+2) = b i := by simp [threefoldNode, Nat.mul_comm, Nat.add_div]

def threefoldScheme {k : ℕ} (s : RSBScheme k) (a b : ℕ → ℝ)
    (hsplit : ∀ i ≤ k+1, s.q i ≤ a i ∧ a i ≤ b i ∧ b i ≤ s.q (i+1)) :
    RSBScheme (3*k+4) where
  m j := s.m (j/3)
  q := threefoldNode s a b
  m_zero := by simpa using s.m_zero
  m_top := by
    rw [show (3*k+4+1)/3=k+1 by omega]
    exact s.m_top
  m_mono j hj := s.m_mono' ((j+1)/3) (by omega) (j/3) (by omega)
  q_zero := by simpa [threefoldNode] using s.q_zero
  q_top := by
    have he : 3*k+4+2=3*(k+2) := by omega
    rw [he,threefoldNode_zero]
    exact s.q_top
  q_mono j hj := by
    have hi : j/3 ≤ k+1 := by omega
    have hre : j=3*(j/3)+j%3 := by omega
    rcases hsplit (j/3) hi with ⟨hqa,hab,hbq⟩
    have hr : j%3<3 := Nat.mod_lt _ (by norm_num)
    rcases (show j%3=0 ∨ j%3=1 ∨ j%3=2 by omega) with h0|h1|h2
    · rw [hre,h0,Nat.add_zero]
      simpa only [threefoldNode_zero,threefoldNode_one] using hqa
    · rw [hre,h1]
      simpa only [show 3*(j/3)+1+1=3*(j/3)+2 by omega,
        threefoldNode_one,threefoldNode_two] using hab
    · rw [hre,h2]
      simpa only [show 3*(j/3)+2+1=3*(j/3+1) by omega,
        threefoldNode_two,threefoldNode_zero] using hbq

@[simp] theorem threefoldScheme_m {k : ℕ} (s : RSBScheme k) (a b : ℕ → ℝ)
    (hsplit : ∀ i ≤ k+1, s.q i ≤ a i ∧ a i ≤ b i ∧ b i ≤ s.q (i+1)) (j : ℕ) :
    (threefoldScheme s a b hsplit).m j=s.m (j/3) := rfl

@[simp] theorem threefoldScheme_q_original {k : ℕ} (s : RSBScheme k) (a b : ℕ → ℝ)
    (hsplit : ∀ i ≤ k+1, s.q i ≤ a i ∧ a i ≤ b i ∧ b i ≤ s.q (i+1)) (i : ℕ) :
    (threefoldScheme s a b hsplit).q (3*i)=s.q i := threefoldNode_zero s a b i

@[simp] theorem threefoldScheme_q_first {k : ℕ} (s : RSBScheme k) (a b : ℕ → ℝ)
    (hsplit : ∀ i ≤ k+1, s.q i ≤ a i ∧ a i ≤ b i ∧ b i ≤ s.q (i+1)) (i : ℕ) :
    (threefoldScheme s a b hsplit).q (3*i+1)=a i := threefoldNode_one s a b i

@[simp] theorem threefoldScheme_q_second {k : ℕ} (s : RSBScheme k) (a b : ℕ → ℝ)
    (hsplit : ∀ i ≤ k+1, s.q i ≤ a i ∧ a i ≤ b i ∧ b i ≤ s.q (i+1)) (i : ℕ) :
    (threefoldScheme s a b hsplit).q (3*i+2)=b i := threefoldNode_two s a b i

private theorem sum_range_three {E : Type*} [AddCommMonoid E] (f : ℕ → E) (n : ℕ) :
    (∑ j ∈ Finset.range (3*n),f j)=
      ∑ i ∈ Finset.range n,(f (3*i)+f (3*i+1)+f (3*i+2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3*(n+1)=((3*n+1)+1)+1 by omega]
    rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,ih,
      Finset.sum_range_succ]
    ac_rfl

private def schemeNode {k : ℕ} (s : RSBScheme k) (i : ℕ) : Paper.Overlap :=
  projIcc 0 1 (by norm_num) (s.q i)

private theorem schemeNode_eq {k : ℕ} (s : RSBScheme k) (i : ℕ) (hi : i≤k+2) :
    (schemeNode s i : ℝ)=s.q i :=
  by
    change (projIcc 0 1 (by norm_num) (s.q i) : ℝ)=s.q i
    rw [projIcc_of_mem (by norm_num : (0 : ℝ)≤1) ⟨s.q_nonneg hi,s.q_le_one hi⟩]

private theorem parisiSchemeRawMeasure_eq_sum_range {k : ℕ} (s : RSBScheme k) :
    Paper.parisiSchemeRawMeasure s = ∑ i ∈ Finset.range (k+1),
      ENNReal.ofReal (s.m (i+1)-s.m i) • Measure.dirac (schemeNode s (i+1)) := by
  unfold Paper.parisiSchemeRawMeasure
  have he (i : Fin (k+1)) : Paper.parisiSchemeAtom s i=schemeNode s (i+1) := by
    apply Subtype.ext
    exact (schemeNode_eq s (i+1) (by omega)).symm
  simp_rw [he]
  exact Fin.sum_univ_eq_sum_range (fun i => ENNReal.ofReal (s.m (i+1)-s.m i) •
    Measure.dirac (schemeNode s (i+1))) _

/-- Inserted same-mass nodes carry zero probability. The resulting atomic
measure is exactly the original measure, including coincident inserted nodes. -/
theorem parisiSchemeMeasure_threefold {k : ℕ} (s : RSBScheme k) (a b : ℕ → ℝ)
    (hsplit : ∀ i ≤ k+1, s.q i ≤ a i ∧ a i ≤ b i ∧ b i ≤ s.q (i+1)) :
    Paper.parisiSchemeMeasure (threefoldScheme s a b hsplit)=Paper.parisiSchemeMeasure s := by
  apply Subtype.ext
  change Paper.parisiSchemeRawMeasure _=Paper.parisiSchemeRawMeasure s
  rw [parisiSchemeRawMeasure_eq_sum_range,parisiSchemeRawMeasure_eq_sum_range]
  let r:=threefoldScheme s a b hsplit
  let f:=fun i=>ENNReal.ofReal (r.m (i+1)-r.m i) • Measure.dirac (schemeNode r (i+1))
  change (∑i∈Finset.range (3*k+4+1),f i)=_
  have hn : 3*k+4+1=(3*(k+1)+1)+1 := by omega
  rw [hn,Finset.sum_range_succ,Finset.sum_range_succ,sum_range_three]
  have hz0 (i : ℕ) : f (3*i)=0 := by
    simp only [f,r,threefoldScheme_m]
    simp [Nat.add_div,Nat.mul_comm]
  have hz1 (i : ℕ) : f (3*i+1)=0 := by
    simp only [f,r,threefoldScheme_m]
    simp [Nat.add_div,Nat.mul_comm]
  rw [show 3*(k+1)+1=3*(k+1)+1 from rfl,hz1,hz0,add_zero,add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hz0,hz1,zero_add,zero_add]
  dsimp only [f]
  have he : schemeNode r (3*i+2+1)=schemeNode s (i+1) := by
    apply Subtype.ext
    change (projIcc 0 1 (by norm_num) (r.q (3*i+2+1)) : ℝ)=_
    simp only [show 3*i+2+1=3*(i+1) by omega,r,threefoldScheme_q_original]
    rfl
  rw [he]
  simp only [r,threefoldScheme_m]
  rw [show (3*i+2+1)/3=i+1 by omega,show (3*i+2)/3=i by omega]

end FourPapersCommon
