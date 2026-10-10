module
public import FourPapersCommon.MonotoneFiniteBins

@[expose] public section

/-! Finite monotone level bins with the upper endpoint assigned to the last
bin. This retains every point while using exactly the prescribed count. -/
noncomputable section
open Set
namespace FourPapersCommon
set_option maxHeartbeats 1000000

def monotoneClosedBinIndex (f : ℝ → ℝ) (a d : ℝ) (N : ℕ) (v : ℝ) : ℕ :=
  min (monotoneBinIndex f a d v) (N - 1)

def monotoneClosedFiniteBin (I : Set ℝ) (f : ℝ → ℝ) (a d : ℝ)
    (N k : ℕ) : Set ℝ := I ∩ {v | monotoneClosedBinIndex f a d N v = k}

theorem monotone_monotoneClosedBinIndex (f : ℝ → ℝ) (hf : Monotone f)
    (a d : ℝ) (hd : 0 < d) (N : ℕ) : Monotone (monotoneClosedBinIndex f a d N) := by
  intro v w hvw
  exact min_le_min (monotone_monotoneBinIndex f hf a d hd hvw) le_rfl

theorem monotoneClosedFiniteBin_ordConnected (I : Set ℝ) (hI : I.OrdConnected)
    (f : ℝ → ℝ) (hf : Monotone f) (a d : ℝ) (hd : 0 < d) (N k : ℕ) :
    (monotoneClosedFiniteBin I f a d N k).OrdConnected :=
  hI.inter (ordConnected_singleton.preimage_mono
    (monotone_monotoneClosedBinIndex f hf a d hd N))

theorem monotoneClosedFiniteBin_subset (I : Set ℝ) (f : ℝ → ℝ)
    (a d : ℝ) (N k : ℕ) : monotoneClosedFiniteBin I f a d N k ⊆ I :=
  inter_subset_left

theorem monotoneClosedBinIndex_lt_count (f : ℝ → ℝ) (a d : ℝ)
    (N : ℕ) (hN : 0 < N) (v : ℝ) : monotoneClosedBinIndex f a d N v < N := by
  exact (min_le_right _ _).trans_lt (by omega)

theorem monotoneClosedFiniteBin_level_range (I : Set ℝ) (f : ℝ → ℝ)
    (a d ell : ℝ) (N k : ℕ) (hd : 0 < d) (hk : k < N)
    (hRange : ∀ v ∈ I, f v ∈ Icc a (a + ell)) (hwidth : ell ≤ (N : ℝ) * d) :
    ∀ v ∈ monotoneClosedFiniteBin I f a d N k,
      f v ∈ Icc (a + (k : ℝ) * d) (a + (k : ℝ) * d + d) := by
  intro v hv
  have hp : 0 ≤ (f v - a) / d := div_nonneg (sub_nonneg.mpr (hRange v hv.1).1) hd.le
  have he : min (monotoneBinIndex f a d v) (N - 1) = k := hv.2
  have hkl : k ≤ monotoneBinIndex f a d v := by omega
  have hl : (k : ℝ) ≤ (f v - a) / d :=
    (Nat.cast_le.mpr hkl).trans (Nat.floor_le hp)
  have hl' := (le_div_iff₀ hd).mp hl
  constructor
  · linarith
  · by_cases hlast : k = N - 1
    · have hcast : (N : ℝ) = (k : ℝ) + 1 := by
        have hh : N = k + 1 := by omega
        exact_mod_cast hh
      have htop := (hRange v hv.1).2
      rw [hcast] at hwidth
      nlinarith
    · have hfloor : monotoneBinIndex f a d v = k := by omega
      have hr := Nat.lt_floor_add_one ((f v - a) / d)
      change (f v - a) / d < (monotoneBinIndex f a d v : ℝ) + 1 at hr
      rw [hfloor] at hr
      have hr' := (div_lt_iff₀ hd).mp hr
      nlinarith

end FourPapersCommon
