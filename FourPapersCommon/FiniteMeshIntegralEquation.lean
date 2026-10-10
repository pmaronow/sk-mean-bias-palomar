module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

@[expose] public section

/-! A genuine cell equation on a finite nondescending mesh implies the
whole interval equation. Repeated nodes produce empty cells. The proof
uses only the integral equation and interval integrability, so continuity
of the value function is not an additional requirement. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
set_option maxHeartbeats 600000

theorem finiteMesh_integralEquation
    (N : ℕ) (q : ℕ → ℝ) (hq : MonotoneOn q (Icc 0 N))
    (hq0 : q 0 = 0) (hqN : q N = 1)
    (f g : ℝ → ℝ) (hg : IntervalIntegrable g volume 0 1)
    (hcell : ∀i, i < N → ∀x ∈ Icc (q i) (q (i+1)),
      ∀y ∈ Icc (q i) (q (i+1)), x ≤ y →
        f y-f x = ∫t in x..y, g t)
    (a b : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1)
    (hab : a ≤ b) :
    f b-f a = ∫t in a..b, g t := by
  have hqm (i : ℕ) (hi : i ≤ N) : q i ∈ Icc (0:ℝ) 1 := by
    constructor
    · rw [←hq0]
      exact hq ⟨le_rfl, Nat.zero_le N⟩ ⟨Nat.zero_le i, hi⟩ (Nat.zero_le i)
    · rw [←hqN]
      exact hq ⟨Nat.zero_le i, hi⟩ ⟨Nat.zero_le N, le_rfl⟩ hi
  have hgsub (x y : ℝ) (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1)
      (hxy : x ≤ y) : IntervalIntegrable g volume x y := by
    apply hg.mono_set
    rw [uIcc_of_le hxy, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc hx.1 hy.2
  have H : ∀i, i ≤ N → ∀z ∈ Icc (0:ℝ) (q i),
      f z-f 0 = ∫t in (0:ℝ)..z, g t := by
    intro i
    induction i with
    | zero =>
        intro hi z hz
        rw [hq0] at hz
        have hz0 : z = 0 := le_antisymm hz.2 hz.1
        simp [hz0]
    | succ i ih =>
        intro hi z hz
        have hiN : i ≤ N := by omega
        by_cases hzi : z ≤ q i
        · exact ih hiN z ⟨hz.1, hzi⟩
        · have hiz : q i ≤ z := le_of_lt (lt_of_not_ge hzi)
          have hstep : q i ≤ q (i+1) := hq
            ⟨Nat.zero_le i, hiN⟩ ⟨Nat.zero_le _, hi⟩ (Nat.le_succ i)
          have hqi := hqm i hiN
          have hqnext := hqm (i+1) hi
          have hz01 : z ∈ Icc (0:ℝ) 1 := ⟨hz.1, hz.2.trans hqnext.2⟩
          have Hprefix := ih hiN (q i) ⟨hqi.1, le_rfl⟩
          have Hpiece := hcell i (by omega) (q i) ⟨le_rfl, hstep⟩
            z ⟨hiz, hz.2⟩ hiz
          calc
            f z-f 0 = (f (q i)-f 0)+(f z-f (q i)) := by ring
            _ = (∫t in (0:ℝ)..q i, g t)+(∫t in q i..z, g t) := by
              rw [Hprefix, Hpiece]
            _ = ∫t in (0:ℝ)..z, g t :=
              intervalIntegral.integral_add_adjacent_intervals
                (hgsub 0 (q i) (by norm_num) hqi hqi.1)
                (hgsub (q i) z hqi hz01 hiz)
  have HA := H N le_rfl a (by simpa only [hqN] using ha)
  have HB := H N le_rfl b (by simpa only [hqN] using hb)
  calc
    f b-f a = (f b-f 0)-(f a-f 0) := by ring
    _ = (∫t in (0:ℝ)..b, g t)-(∫t in (0:ℝ)..a, g t) := by rw [HB, HA]
    _ = ∫t in a..b, g t := intervalIntegral.integral_interval_sub_left
      (hgsub 0 b (by norm_num) hb hb.1) (hgsub 0 a (by norm_num) ha ha.1)

end FourPapersCommon
