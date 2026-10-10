module
public import QuantitativePaper.VectorSitePrefixFunctions

@[expose] public section

/-! Exact discrete Stieltjes telescope of the true prefix log density.
Every coefficient is retained, including the initial disorder tilt. -/
noncomputable section
open Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

def prefixMassIncrement {k : ℕ} (s : RSBScheme k) (a : ℝ) (j : ℕ) : ℝ :=
  if j=0 then s.m 0-a else s.m j-s.m (j-1)

def discretePrefixWeight (m : ℕ→ℝ) (a : ℝ) : (N : ℕ)→(Fin (N+1)→ℝ)→ℝ
  | 0,u => a*u 0
  | N+1,u => discretePrefixWeight m a N (fun j=>u j.castSucc)+
      m N*(u (Fin.last (N+1))-u (Fin.last N).castSucc)

theorem discretePrefixWeight_telescope {k : ℕ} (s : RSBScheme k) (a : ℝ)
    (N : ℕ) (hN : 0<N) (u : Fin (N+1)→ℝ) :
    discretePrefixWeight s.m a N u=s.m (N-1)*u (Fin.last N)-
      ∑ j : Fin N,prefixMassIncrement s a j*u j.castSucc := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h0 : N=0
    · subst N
      simp [discretePrefixWeight,prefixMassIncrement]
      ring
    · have hp : 0<N := by omega
      rw [discretePrefixWeight,ih hp,Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last,
        Nat.add_sub_cancel,prefixMassIncrement,dif_neg h0]
      rw [if_neg h0]
      ring

theorem prefixMassIncrement_nonneg {k : ℕ} (s : RSBScheme k) (a : ℝ)
    (ha : a ≤ s.m 0) (j : ℕ) (hj : j ≤ k+1) : 0 ≤ prefixMassIncrement s a j := by
  unfold prefixMassIncrement
  split_ifs with h0
  · exact sub_nonneg.mpr ha
  · exact sub_nonneg.mpr (s.m_mono' j hj (j-1) (Nat.sub_le _ _))

theorem sum_prefixMassIncrement {k : ℕ} (s : RSBScheme k) (a : ℝ)
    (N : ℕ) (hN : 0<N) :
    (∑ j : Fin N,prefixMassIncrement s a j)=s.m (N-1)-a := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h0 : N=0
    · subst N
      simp [prefixMassIncrement]
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last]
      rw [ih (by omega)]
      simp only [prefixMassIncrement,if_neg h0,Nat.add_sub_cancel]
      ring

theorem vectorPrefixLogWeight_eq_discrete {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (N : ℕ) (h : FiniteHistory (VectorState n) N) :
    vectorPrefixLogWeight s β t a N h=discretePrefixWeight s.m a N
      (fun j=>vectorRecursion s β t (h j).1 (k+2-j.val) (h j).2) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [vectorPrefixLogWeight,discretePrefixWeight]
    dsimp only
    rw [ih]
    have hn : k+2-(N+1)=k+1-N := by omega
    simp only [Fin.val_last,Fin.val_castSucc,hn]
    rfl

theorem vectorPrefixLogWeight_stieltjes {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (N : ℕ) (hN : 0<N) (h : FiniteHistory (VectorState n) N) :
    vectorPrefixLogWeight s β t a N h =
      s.m (N-1)*vectorRecursion s β t (h (Fin.last N)).1 (k+2-N)
        (h (Fin.last N)).2-
      ∑ j : Fin N,prefixMassIncrement s a j*
        vectorRecursion s β t (h j.castSucc).1 (k+2-j.val) (h j.castSucc).2 := by
  rw [vectorPrefixLogWeight_eq_discrete,discretePrefixWeight_telescope s a N hN]
  rfl

end QuantitativePaper
