module
public import QuantitativeFollowup.FollowupCavityGeneratedMarkProgramBudget
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

@[expose] public section

/-! The normalized marginal budget depends only on structural counts.
The Gaussian interpolation prefactors are deliberately absent. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup.CavityGeneratedMarkProgram
variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

def constructorCount : {m : ℕ} → CavityGeneratedMarkProgram Q m → ℕ
  | _, .initial => 0
  | _, .fresh P _ => P.constructorCount + 1
  | _, .atom P _ _ => P.constructorCount + 1
  | _, .inherited P _ _ _ _ => P.constructorCount + 1
  | _, .attenuate P _ _ => P.constructorCount + 1
  | _, .restrict P _ => P.constructorCount + 1
  | _, .add P R => P.constructorCount + R.constructorCount + 1

def largestMultiplicity : {m : ℕ} → CavityGeneratedMarkProgram Q m → ℕ
  | _, .initial => 0
  | _, .fresh P _ => P.largestMultiplicity
  | _, .atom P _ _ => P.largestMultiplicity
  | _, .inherited P _ k _ _ => max k P.largestMultiplicity
  | _, .attenuate P _ _ => P.largestMultiplicity
  | _, .restrict P _ => P.largestMultiplicity
  | _, .add P R => max P.largestMultiplicity R.largestMultiplicity

theorem markCount_le_constructorCount_succ {m : ℕ}
    (P : CavityGeneratedMarkProgram Q m) : m ≤ P.constructorCount + 1 := by
  induction P with
  | initial => simp only [constructorCount]; omega
  | fresh P E ih => simp only [constructorCount]; omega
  | atom P q hq ih => simp only [constructorCount]; omega
  | inherited P i k w hw ih => simp only [constructorCount]; omega
  | attenuate P w hw ih => simp only [constructorCount]; omega
  | restrict P E ih => simp only [constructorCount]; omega
  | add P R ihP ihR => simp only [constructorCount]; omega

theorem budget_le_count_power {m : ℕ} (P : CavityGeneratedMarkProgram Q m)
    (L : ℕ) (hL : P.largestMultiplicity ≤ L) :
    P.budget ≤ (L + 2) ^ P.constructorCount := by
  have hbase (j : ℕ) : 1 ≤ j + 2 := by omega
  induction P generalizing L with
  | initial => simp only [budget, constructorCount, pow_zero, le_refl]
  | fresh P E ih =>
      exact (ih L hL).trans (pow_le_pow_right' (hbase L) (Nat.le_succ _))
  | atom P q hq ih =>
      exact (ih L hL).trans (pow_le_pow_right' (hbase L) (Nat.le_succ _))
  | inherited P i k w hw ih =>
      change max k P.largestMultiplicity ≤ L at hL
      have hk : k ≤ L + 2 := (le_of_max_le_left hL).trans (by omega)
      have hp := ih L (le_of_max_le_right hL)
      change k * P.budget ≤ (L + 2) ^ (P.constructorCount + 1)
      rw [pow_succ]
      simpa only [mul_comm] using Nat.mul_le_mul hk hp
  | attenuate P w hw ih =>
      exact (ih L hL).trans (pow_le_pow_right' (hbase L) (Nat.le_succ _))
  | restrict P E ih =>
      exact (ih L hL).trans (pow_le_pow_right' (hbase L) (Nat.le_succ _))
  | add P R ihP ihR =>
      change max P.largestMultiplicity R.largestMultiplicity ≤ L at hL
      have hp := (ihP L (le_of_max_le_left hL)).trans
        (pow_le_pow_right' (hbase L) (Nat.le_add_right P.constructorCount R.constructorCount))
      have hr := (ihR L (le_of_max_le_right hL)).trans
        (pow_le_pow_right' (hbase L) (Nat.le_add_left R.constructorCount P.constructorCount))
      change P.budget + R.budget ≤ (L + 2) ^ (P.constructorCount + R.constructorCount + 1)
      rw [pow_succ]
      have hs : P.budget + R.budget ≤ 2 * (L + 2) ^ (P.constructorCount + R.constructorCount) := by
        omega
      have ht : 2 ≤ L + 2 := by omega
      have hm := Nat.mul_le_mul_right
        ((L + 2) ^ (P.constructorCount + R.constructorCount)) ht
      exact hs.trans (by simpa only [mul_comm] using hm)

theorem coordinate_marginal_le_count_power (ν : Measure Q) [SFinite ν]
    (hν : ν univ ≤ 1) {m : ℕ} (P : CavityGeneratedMarkProgram Q m)
    (L : ℕ) (hL : P.largestMultiplicity ≤ L) (i : Fin m) :
    (P.measure ν).map (fun h => h i) ≤ ((L + 2) ^ P.constructorCount : ℝ≥0∞) • ν := by
  apply (P.coordinate_marginal_le_budget ν hν i).trans
  apply cavityGenerated_smul_mono
  exact_mod_cast P.budget_le_count_power L hL

end QuantitativeFollowup.CavityGeneratedMarkProgram
