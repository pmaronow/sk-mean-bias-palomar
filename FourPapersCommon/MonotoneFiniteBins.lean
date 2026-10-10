module
public import FourPapersCommon.MonotoneBinIntervals
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

/-! A genuine finite partition into narrow level bins for a monotone real
function.  The final endpoint is retained without changing the bin width. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1000000

def monotoneBinIndex (f : ℝ→ℝ) (a d v : ℝ) : ℕ:=⌊(f v-a)/d⌋₊

def monotoneFiniteBin (I : Set ℝ) (f : ℝ→ℝ) (a d : ℝ) (k : ℕ) : Set ℝ:=
  I∩{v | monotoneBinIndex f a d v=k}

theorem monotone_monotoneBinIndex (f : ℝ→ℝ) (hf : Monotone f) (a d : ℝ) (hd : 0<d) :
    Monotone (monotoneBinIndex f a d) := by
  intro v w hvw
  exact Nat.floor_mono (div_le_div_of_nonneg_right (sub_le_sub_right (hf hvw) a) hd.le)

theorem monotoneFiniteBin_ordConnected (I : Set ℝ) (hI : I.OrdConnected)
    (f : ℝ→ℝ) (hf : Monotone f) (a d : ℝ) (hd : 0<d) (k : ℕ) :
    (monotoneFiniteBin I f a d k).OrdConnected :=
  hI.inter (ordConnected_singleton.preimage_mono (monotone_monotoneBinIndex f hf a d hd))

theorem monotoneFiniteBin_subset (I : Set ℝ) (f : ℝ→ℝ) (a d : ℝ) (k : ℕ) :
    monotoneFiniteBin I f a d k⊆I :=inter_subset_left

theorem monotoneFiniteBin_level_range (I : Set ℝ) (f : ℝ→ℝ) (a d : ℝ)
    (hd : 0<d) (hlo : ∀v∈I,a≤f v) (k : ℕ) :
    ∀v∈monotoneFiniteBin I f a d k,f v∈Icc (a+(k:ℝ)*d) (a+(k:ℝ)*d+d) := by
  intro v hv
  have hp : 0≤(f v-a)/d:=div_nonneg (sub_nonneg.mpr (hlo v hv.1)) hd.le
  have hl:=Nat.floor_le hp
  have hr:=Nat.lt_floor_add_one ((f v-a)/d)
  have he : ⌊(f v-a)/d⌋₊=k:=hv.2
  rw [he] at hl hr
  have hl':=(le_div_iff₀ hd).mp hl
  have hr':=(div_lt_iff₀ hd).mp hr
  constructor <;> linarith

theorem monotoneBinIndex_lt_count (f : ℝ→ℝ) (a d ell v : ℝ)
    (hd : 0<d) (hRange : f v∈Icc a (a+ell)) :
    monotoneBinIndex f a d v<Nat.ceil (ell/d)+1 := by
  have hl : (f v-a)/d≤ell/d:=div_le_div_of_nonneg_right (by linarith [hRange.2]) hd.le
  exact Nat.lt_succ_of_le ((Nat.floor_mono hl).trans (Nat.floor_le_ceil _))

theorem monotoneFiniteBins_cover (I : Set ℝ) (f : ℝ→ℝ) (a d ell : ℝ)
    (hd : 0<d) (hRange : ∀v∈I,f v∈Icc a (a+ell)) :
    I=⋃k∈Finset.range (Nat.ceil (ell/d)+1),monotoneFiniteBin I f a d k := by
  ext v
  constructor
  · intro hv
    exact mem_iUnion.mpr ⟨monotoneBinIndex f a d v,mem_iUnion.mpr
      ⟨Finset.mem_range.mpr (monotoneBinIndex_lt_count f a d ell v hd (hRange v hv)),⟨hv,rfl⟩⟩⟩
  · intro hv
    rcases mem_iUnion.mp hv with ⟨k,hk⟩
    rcases mem_iUnion.mp hk with ⟨_,hv⟩
    exact hv.1

theorem monotoneFiniteBins_pairwiseDisjoint (I : Set ℝ) (f : ℝ→ℝ) (a d : ℝ) :
    Pairwise (fun i j : ℕ=>Disjoint (monotoneFiniteBin I f a d i) (monotoneFiniteBin I f a d j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hvi hvj
  exact hij (hvi.2.symm.trans hvj.2)

theorem monotoneFiniteBins_count_bound (d ell : ℝ) (hd : 0<d) (hell : 0≤ell) :
    (Nat.ceil (ell/d)+1:ℕ)≤ell/d+2 := by
  have h:=Nat.ceil_lt_add_one (div_nonneg hell hd.le)
  simp only [Nat.cast_add,Nat.cast_one]
  linarith

end FourPapersCommon
