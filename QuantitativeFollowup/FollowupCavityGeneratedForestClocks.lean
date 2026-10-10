module
public import QuantitativeFollowup.FollowupCavityGeneratedForestCubic

@[expose] public section

/-! Structural clocks of a marked forest. Every genuine branch carries
an earlier history coordinate. Order restrictions are implemented by an
actual measure restriction; a continuous clipped clock supplies the
same retained levels on that restriction. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {m : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

inductive CavityGeneratedClockLabel (m : ℕ)
  | terminal
  | initial
  | mark (i : Fin m)

def CavityGeneratedClockLabel.value (l : CavityGeneratedClockLabel m)
    (h : CavityGeneratedHistory Paper.Overlap m) : Paper.Overlap :=
  match l with
  | .terminal => 1
  | .initial => 0
  | .mark i => h i

theorem CavityGeneratedClockLabel.continuous_value (l : CavityGeneratedClockLabel m) :
    Continuous l.value := by
  cases l with
  | terminal => exact continuous_const
  | initial => exact continuous_const
  | mark i => exact continuous_apply i

def cavityGeneratedClippedClock (q : ℕ → Paper.Overlap) : ℕ → Paper.Overlap
  | 0 => q 0
  | j+1 => min (cavityGeneratedClippedClock q j) (q (j+1))

theorem cavityGeneratedClippedClock_step_le (q : ℕ → Paper.Overlap) (j : ℕ) :
    cavityGeneratedClippedClock q (j+1) ≤ cavityGeneratedClippedClock q j := min_le_left _ _

theorem cavityGeneratedClippedClock_eq (q : ℕ → Paper.Overlap) (J : ℕ)
    (hmono : ∀j, j < J → q (j+1) ≤ q j) (j : ℕ) (hj : j ≤ J) :
    cavityGeneratedClippedClock q j = q j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change min (cavityGeneratedClippedClock q j) (q (j+1)) = q (j+1)
      rw [ih (by omega)]
      exact min_eq_right (hmono j (by omega))

theorem cavityGeneratedClippedClock_continuous
    {H : Type*} [TopologicalSpace H] (q : H → ℕ → Paper.Overlap)
    (hq : ∀j, Continuous (fun h => q h j)) (j : ℕ) :
    Continuous (fun h => cavityGeneratedClippedClock (q h) j) := by
  induction j with
  | zero => exact hq 0
  | succ j ih => exact ih.min (hq (j+1))

structure CavityGeneratedForestClockTemplate (m : ℕ) where
  componentCount : ℕ
  depth : Fin componentCount → ℕ
  tree : (c : Fin componentCount) → FiniteTerminalGenealogy (depth c)
  label : (c : Fin componentCount) → Fin (depth c + 1) → CavityGeneratedClockLabel m
  terminal_label : ∀c, label c 0 = .terminal
  initial_label : ∀c, label c (Fin.last (depth c)) = .initial
  branch_label : ∀c (b e : ObservationLeaf (tree c)), b ≠ e → ∃i : Fin m,
    label c ⟨observationCommonLevel (tree c) b e,
      by have hh := cavityGenerated_observationCommonLevel_le (tree c) b e; omega⟩ = .mark i

namespace CavityGeneratedForestClockTemplate

def rawClock (W : CavityGeneratedForestClockTemplate m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) (j : ℕ) : Paper.Overlap :=
  if hj : j ≤ W.depth c then (W.label c ⟨j, by omega⟩).value h else 0

def clock (W : CavityGeneratedForestClockTemplate m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) : ℕ → Paper.Overlap :=
  cavityGeneratedClippedClock (W.rawClock h c)

theorem rawClock_continuous (W : CavityGeneratedForestClockTemplate m)
    (c : Fin W.componentCount) (j : ℕ) : Continuous (fun h => W.rawClock h c j) := by
  by_cases hj : j ≤ W.depth c
  · simpa only [rawClock, dif_pos hj] using (W.label c ⟨j, by omega⟩).continuous_value
  · simpa only [rawClock, dif_neg hj] using (continuous_const (y:=(0:Paper.Overlap)))

theorem clock_continuous (W : CavityGeneratedForestClockTemplate m)
    (c : Fin W.componentCount) (j : ℕ) : Continuous (fun h => W.clock h c j) :=
  cavityGeneratedClippedClock_continuous (fun h => W.rawClock h c)
    (fun p => W.rawClock_continuous c p) j

theorem clock_step_le (W : CavityGeneratedForestClockTemplate m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) (j : ℕ) :
    W.clock h c (j+1) ≤ W.clock h c j := cavityGeneratedClippedClock_step_le _ _

theorem rawClock_terminal (W : CavityGeneratedForestClockTemplate m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) :
    W.rawClock h c 0 = 1 := by
  simp only [rawClock, Nat.zero_le, ↓reduceDIte]
  change (W.label c 0).value h = 1
  rw [W.terminal_label]
  rfl

theorem rawClock_initial (W : CavityGeneratedForestClockTemplate m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) :
    W.rawClock h c (W.depth c) = 0 := by
  simp only [rawClock, le_refl, ↓reduceDIte]
  have he : (⟨W.depth c, by omega⟩ : Fin (W.depth c + 1)) = Fin.last (W.depth c) := by
    apply Fin.ext; rfl
  rw [he, W.initial_label]
  rfl

theorem clock_terminal (W : CavityGeneratedForestClockTemplate m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) :
    W.clock h c 0 = 1 := W.rawClock_terminal h c

theorem clock_initial (W : CavityGeneratedForestClockTemplate m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) :
    W.clock h c (W.depth c) = 0 := by
  rcases hdep : W.depth c with _|d
  · change W.rawClock h c 0 = 0
    simpa only [hdep] using W.rawClock_initial h c
  · change min (cavityGeneratedClippedClock (W.rawClock h c) d) (W.rawClock h c (d+1)) = 0
    rw [show W.rawClock h c (d+1) = 0 from by simpa only [hdep] using W.rawClock_initial h c]
    apply min_eq_right
    change (0:ℝ) ≤ (cavityGeneratedClippedClock (W.rawClock h c) d : ℝ)
    exact (cavityGeneratedClippedClock (W.rawClock h c) d).property.1

def orderSet (W : CavityGeneratedForestClockTemplate m) :
    Set (CavityGeneratedHistory Paper.Overlap m) :=
  {h | ∀c, ∀j : Fin (W.depth c), W.rawClock h c (j+1) ≤ W.rawClock h c j}

theorem isClosed_orderSet (W : CavityGeneratedForestClockTemplate m) : IsClosed W.orderSet := by
  change IsClosed {h | ∀c, ∀j : Fin (W.depth c), W.rawClock h c (j+1) ≤ W.rawClock h c j}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro c
  apply isClosed_iInter
  intro j
  exact isClosed_le (W.rawClock_continuous c (j+1)) (W.rawClock_continuous c j)

theorem clock_eq_raw_of_mem (W : CavityGeneratedForestClockTemplate m)
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h ∈ W.orderSet)
    (c : Fin W.componentCount) (j : ℕ) (hj : j ≤ W.depth c) :
    W.clock h c j = W.rawClock h c j := by
  apply cavityGeneratedClippedClock_eq _ (W.depth c) _ j hj
  intro p hp
  exact hh c ⟨p, hp⟩

theorem branch_clock_is_mark (W : CavityGeneratedForestClockTemplate m)
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h ∈ W.orderSet)
    (c : Fin W.componentCount) (b e : ObservationLeaf (W.tree c)) (hbe : b ≠ e) :
    ∃i : Fin m, W.clock h c (observationCommonLevel (W.tree c) b e) = h i := by
  have hj := cavityGenerated_observationCommonLevel_le (W.tree c) b e
  obtain ⟨i, hi⟩ := W.branch_label c b e hbe
  refine ⟨i, ?_⟩
  rw [W.clock_eq_raw_of_mem h hh c _ hj]
  simp only [rawClock, dif_pos hj]
  rw [hi]
  rfl

end CavityGeneratedForestClockTemplate
end QuantitativeFollowup
