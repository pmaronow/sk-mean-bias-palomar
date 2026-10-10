module
public import FourPapersCommon.ThreefoldSchemeRefinement

@[expose] public section

/-! Arbitrarily many repeated finite-profile nodes. The atomic probability
measure is preserved exactly; the extra nodes carry no new mass. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace FourPapersCommon
open SpinGlass.Targets
set_option maxHeartbeats 900000

def repeatNodeIndex (C p : ℕ) : ℕ := (p+C-1)/C

/-- Every old node is repeated C times, with the right endpoint of each
cell retained. At least two copies ensure the backend depth is valid. -/
def repeatNodeScheme {k : ℕ} (s : RSBScheme k) (C : ℕ) (hC : 2 ≤ C) :
    RSBScheme (C*(k+2)-2) where
  q p := s.q (min (repeatNodeIndex C p) (k+2))
  m p := s.m (min (p/C) (k+1))
  m_zero := by simp [s.m_zero]
  m_top := by
    have hn : C*(k+2)-2+1=C*(k+1)+(C-1) := by
      have he : C*(k+2)=C*(k+1)+C := by ring
      omega
    have hd : (C*(k+1)+(C-1))/C=k+1 := by
      rw [Nat.mul_add_div (by omega : 0<C)]
      simp [Nat.div_eq_of_lt (by omega : C-1<C)]
    simp only [hn,hd,min_self,s.m_top]
  m_mono p hp := s.m_mono' _ (min_le_right _ _) _
    (min_le_min_right _ (Nat.div_le_div_right (Nat.le_succ p)))
  q_zero := by
    have hz : repeatNodeIndex C 0=0 := by
      simp only [repeatNodeIndex,zero_add]
      exact Nat.div_eq_of_lt (by omega)
    simp [hz,s.q_zero]
  q_top := by
    have hn : C*(k+2)-2+2=C*(k+2) := by
      have : 2≤C*(k+2) := by nlinarith
      omega
    have hd : repeatNodeIndex C (C*(k+2))=k+2 := by
      unfold repeatNodeIndex
      rw [show C*(k+2)+C-1=C*(k+2)+(C-1) by omega, Nat.mul_add_div (by omega : 0<C)]
      simp [Nat.div_eq_of_lt (by omega : C-1<C)]
    simp only [hn,hd,min_self,s.q_top]
  q_mono p hp := s.q_mono' _ (min_le_right _ _) _
    (min_le_min_right _ (Nat.div_le_div_right (by omega)))

@[simp] theorem repeatNodeScheme_depth {k : ℕ} (s : RSBScheme k) (C : ℕ) (hC : 2≤C) :
    C*(k+2)-2+2=C*(k+2) := by
  have : 2≤C*(k+2) := by nlinarith
  omega

@[simp] theorem repeatNodeScheme_m {k : ℕ} (s : RSBScheme k) (C : ℕ) (hC : 2≤C) (p : ℕ) :
    (repeatNodeScheme s C hC).m p=s.m (min (p/C) (k+1)) := rfl

@[simp] theorem repeatNodeScheme_q_original {k : ℕ} (s : RSBScheme k) (C : ℕ)
    (hC : 2≤C) (i : ℕ) (hi : i≤k+2) :
    (repeatNodeScheme s C hC).q (C*i)=s.q i := by
  change s.q (min ((C*i+C-1)/C) (k+2))=s.q i
  have he : (C*i+C-1)/C=i := by
    rw [show C*i+C-1=C*i+(C-1) by omega,Nat.mul_add_div (by omega : 0<C)]
    simp [Nat.div_eq_of_lt (by omega : C-1<C)]
  rw [he,min_eq_left hi]

theorem repeatNodeScheme_q_backward_block {k : ℕ} (s : RSBScheme k) (C : ℕ)
    (hC : 2≤C) (b t : ℕ) (hb : b≤k+1) (ht : t<C) :
    (repeatNodeScheme s C hC).q (C*(k+2)-(C*b+t))=s.q (k+2-b) := by
  change s.q (min ((C*(k+2)-(C*b+t)+C-1)/C) (k+2))=_
  have he : C*(k+2)-(C*b+t)+C-1=C*(k+2-b)+(C-1-t) := by
    have hh : C*(k+2-b)+C*b=C*(k+2) := by
      rw [←Nat.mul_add,Nat.sub_add_cancel (by omega : b≤k+2)]
    have hl : C*b+t ≤ C*(k+2) := by nlinarith
    omega
  rw [he,Nat.mul_add_div (by omega : 0<C),
    Nat.div_eq_of_lt (by omega : C-1-t<C),add_zero,min_eq_left (Nat.sub_le _ _)]

private def repeatSchemeNode {k : ℕ} (s : RSBScheme k) (i : ℕ) : Paper.Overlap :=
  projIcc 0 1 zero_le_one (s.q i)

private theorem repeatSchemeNode_eq {k : ℕ} (s : RSBScheme k) (i : ℕ) (hi : i≤k+2) :
    (repeatSchemeNode s i : ℝ)=s.q i := by
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨s.q_nonneg hi,s.q_le_one hi⟩)

private theorem repeatSchemeRaw_sum {k : ℕ} (s : RSBScheme k) :
    Paper.parisiSchemeRawMeasure s=∑i∈Finset.range (k+1),
      ENNReal.ofReal (s.m (i+1)-s.m i) • Measure.dirac (repeatSchemeNode s (i+1)) := by
  unfold Paper.parisiSchemeRawMeasure
  have he (i : Fin (k+1)) : Paper.parisiSchemeAtom s i=repeatSchemeNode s (i+1) := by
    apply Subtype.ext
    exact (repeatSchemeNode_eq s (i+1) (by omega)).symm
  simp_rw [he]
  exact Fin.sum_univ_eq_sum_range (fun i=> ENNReal.ofReal (s.m (i+1)-s.m i) •
    Measure.dirac (repeatSchemeNode s (i+1))) _

private theorem sum_range_blocks {E : Type*} [AddCommMonoid E] (f : ℕ→E) (C N : ℕ) :
    (∑i∈Finset.range (C*N),f i)=∑j∈Finset.range N,∑t∈Finset.range C,f (C*j+t) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,ih,Finset.sum_range_succ]

theorem parisiSchemeMeasure_repeatNodeScheme {k : ℕ} (s : RSBScheme k) (C : ℕ)
    (hC : 2≤C) : Paper.parisiSchemeMeasure (repeatNodeScheme s C hC)=Paper.parisiSchemeMeasure s := by
  apply Subtype.ext
  change Paper.parisiSchemeRawMeasure _=Paper.parisiSchemeRawMeasure s
  rw [repeatSchemeRaw_sum,repeatSchemeRaw_sum]
  let r:=repeatNodeScheme s C hC
  let f:=fun p=>ENNReal.ofReal (r.m (p+1)-r.m p) • Measure.dirac (repeatSchemeNode r (p+1))
  change (∑p∈Finset.range (C*(k+2)-2+1),f p)=_
  have hz (i t : ℕ) (ht : t<C-1) : f (C*i+t)=0 := by
    have hd : (C*i+t)/C=i := by
      rw [Nat.mul_add_div (by omega : 0<C),Nat.div_eq_of_lt (by omega : t<C),add_zero]
    have hd' : (C*i+t+1)/C=i := by
      rw [show C*i+t+1=C*i+(t+1) by omega,Nat.mul_add_div (by omega : 0<C),Nat.div_eq_of_lt (by omega : t+1<C),add_zero]
    simp [f,r,repeatNodeScheme_m,hd,hd']
  have hlast (i : ℕ) (hi : i≤k+1) : f (C*i+(C-1))=
      ENNReal.ofReal (s.m (min (i+1) (k+1))-s.m (min i (k+1))) •
        Measure.dirac (repeatSchemeNode s (i+1)) := by
    have hd : (C*i+(C-1))/C=i := by
      rw [Nat.mul_add_div (by omega : 0<C),
        Nat.div_eq_of_lt (by omega : C-1<C),add_zero]
    have he : C*i+(C-1)+1=C*(i+1) := by
      have : C*(i+1)=C*i+C := by ring
      omega
    have hnode : repeatSchemeNode r (C*(i+1))=repeatSchemeNode s (i+1) := by
      apply Subtype.ext
      unfold repeatSchemeNode
      rw [show r.q (C*(i+1))=s.q (i+1) from repeatNodeScheme_q_original s C hC _ (by omega)]
    simp only [f,r,repeatNodeScheme_m,he,hd,
      Nat.mul_div_cancel_left _ (by omega : 0<C),hnode]
  have hfull : (∑p∈Finset.range (C*(k+2)-2+1),f p)=∑p∈Finset.range (C*(k+2)),f p := by
    have hn : C*(k+2)=(C*(k+2)-2+1)+1 := by
      have : 2≤C*(k+2) := by nlinarith
      omega
    conv_rhs => rw [hn,Finset.sum_range_succ]
    have he : C*(k+2)-2+1=C*(k+1)+(C-1) := by
      have : C*(k+2)=C*(k+1)+C := by ring
      omega
    rw [he,hlast (k+1) (by omega)]
    simp
  rw [hfull,sum_range_blocks]
  have hblock (i : ℕ) (hi : i≤k+1) : (∑t∈Finset.range C,f (C*i+t))=f (C*i+(C-1)) := by
    apply Finset.sum_eq_single (C-1)
    · intro t ht hne
      exact hz i t (by have := Finset.mem_range.mp ht; omega)
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  rw [Finset.sum_range_succ]
  have htop : (∑t∈Finset.range C,f (C*(k+1)+t))=0 := by
    rw [hblock _ (by omega),hlast _ (by omega)]
    simp
  rw [htop,add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hblock _ (by have := Finset.mem_range.mp hi; omega),
    hlast _ (by have := Finset.mem_range.mp hi; omega),
    min_eq_left (by have := Finset.mem_range.mp hi; omega : i+1≤k+1),
    min_eq_left (by have := Finset.mem_range.mp hi; omega : i≤k+1)]

end FourPapersCommon
