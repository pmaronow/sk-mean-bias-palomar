module
public import QuantitativeFollowup.ConcentratingResponseTest
public import FourPapersCommon.FiniteTriangleCutoff

@[expose] public section

/-! Literal finite disjoint families of concentrating C¹ tests. They
provide a smooth global response test directly, retaining exact area and
Dirichlet energy and every boundary atom. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 2000000

def finiteConcentratingBump (S : Finset ℕ) (a : ℕ → ℝ) (ell x : ℝ) : ℝ :=
  ∑i∈S, concentratingIntervalBump (a i) ell x

def finiteConcentratingSlope (S : Finset ℕ) (a : ℕ → ℝ) (ell x : ℝ) : ℝ :=
  ∑i∈S, concentratingIntervalIncrement (a i) ell x

theorem continuous_finiteConcentratingBump (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ) :
    Continuous (finiteConcentratingBump S a ell) :=
  continuous_finsetSum S (fun i _ => (contDiff_concentratingIntervalBump (a i) ell).continuous)

theorem continuous_finiteConcentratingSlope (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ) (hell : 0 < ell) :
    Continuous (finiteConcentratingSlope S a ell) :=
  continuous_finsetSum S (fun i _ => (lipschitz_concentratingIntervalIncrement (a i) ell hell).continuous)

theorem hasDerivAt_finiteConcentratingBump (S : Finset ℕ) (a : ℕ → ℝ) (ell x : ℝ) :
    HasDerivAt (finiteConcentratingBump S a ell) (finiteConcentratingSlope S a ell x) x :=
  by
    convert! HasDerivAt.fun_sum (u:=S)
      (fun i _ => hasDerivAt_concentratingIntervalBump (a i) ell x) using 1

theorem finiteConcentratingBump_nonneg (S : Finset ℕ) (a : ℕ → ℝ) (ell x : ℝ) :
    0 ≤ finiteConcentratingBump S a ell x :=
  Finset.sum_nonneg (fun i _ => (concentratingIntervalBump_bounds (a i) ell x).1)

theorem finiteConcentratingBump_zero_outside (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell) (x : ℝ) (hx : x∉⋃i∈S, Ioo (a i) (a i+ell)) :
    finiteConcentratingBump S a ell x=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact concentratingIntervalBump_zero_outside (a i) ell x hell
    (fun h => hx (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,h⟩⟩))

theorem finiteConcentratingBump_le_one (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell)
    (hdisj : (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (a i) (a i+ell))) (x : ℝ) :
    finiteConcentratingBump S a ell x ≤ 1 := by
  classical
  by_cases hx : ∃i∈S, x∈Ioo (a i) (a i+ell)
  · obtain ⟨i,hi,hxi⟩ := hx
    have he : finiteConcentratingBump S a ell x=concentratingIntervalBump (a i) ell x := by
      apply Finset.sum_eq_single_of_mem i hi
      intro j hj hji
      exact concentratingIntervalBump_zero_outside (a j) ell x hell
        (fun hxj => (Set.disjoint_left.mp (hdisj hi hj hji.symm)) hxi hxj)
    rw [he]
    exact (concentratingIntervalBump_bounds (a i) ell x).2
  · have hxu : x∉⋃i∈S, Ioo (a i) (a i+ell) := by
      intro hu
      obtain ⟨i,hi⟩ := mem_iUnion.mp hu
      obtain ⟨his,hxi⟩ := mem_iUnion.mp hi
      exact hx ⟨i,his,hxi⟩
    rw [finiteConcentratingBump_zero_outside S a ell hell x hxu]
    norm_num

def finiteConcentratingResponseTest (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell) (ha : ∀i∈S,0 ≤ a i) (he : ∀i∈S,a i+ell ≤ 1) : ResponseC1Test where
  value := finiteConcentratingBump S a ell
  slope := finiteConcentratingSlope S a ell
  continuous := continuous_finiteConcentratingBump S a ell
  continuous_slope := continuous_finiteConcentratingSlope S a ell hell
  hasDerivAt := hasDerivAt_finiteConcentratingBump S a ell
  zero_left := by
    apply Finset.sum_eq_zero
    intro i hi
    exact concentratingIntervalBump_zero_outside (a i) ell 0 hell
      (fun hx => not_lt_of_ge (ha i hi) hx.1)
  zero_right := by
    apply Finset.sum_eq_zero
    intro i hi
    exact concentratingIntervalBump_zero_outside (a i) ell 1 hell
      (fun hx => not_lt_of_ge (he i hi) hx.2)

theorem finiteConcentratingBump_unit_integral (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell) (ha : ∀i∈S,0 ≤ a i) (he : ∀i∈S,a i+ell ≤ 1) :
    (∫x in (0 : ℝ)..1, finiteConcentratingBump S a ell x) = (S.card : ℝ)*8*ell/15 := by
  unfold finiteConcentratingBump
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (contDiff_concentratingIntervalBump (a i) ell).continuous.intervalIntegrable 0 1)]
  rw [Finset.sum_congr rfl (fun i hi => concentratingIntervalBump_unit_integral
    (a i) ell hell (ha i hi) (he i hi))]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

theorem finiteConcentratingSlope_square (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell)
    (hdisj : (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (a i) (a i+ell))) (x : ℝ) :
    (finiteConcentratingSlope S a ell x)^2=∑i∈S,(concentratingIntervalIncrement (a i) ell x)^2 := by
  apply FourPapersCommon.sq_sum_of_pairwise_products_zero
  intro i hi j hj hij
  by_cases hxi : x∈Ioo (a i) (a i+ell)
  · have hxj : x∉Ioo (a j) (a j+ell) :=
      fun hxj => (Set.disjoint_left.mp (hdisj hi hj hij)) hxi hxj
    rw [concentratingIntervalIncrement_zero_outside (a j) ell x hell hxj,mul_zero]
  · rw [concentratingIntervalIncrement_zero_outside (a i) ell x hell hxi,zero_mul]

theorem finiteConcentratingSlope_unit_energy (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell) (ha : ∀i∈S,0 ≤ a i) (he : ∀i∈S,a i+ell ≤ 1)
    (hdisj : (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (a i) (a i+ell))) :
    (∫x in (0 : ℝ)..1,(finiteConcentratingSlope S a ell x)^2) =
      (S.card : ℝ)*512/(105*ell) := by
  rw [intervalIntegral.integral_congr (fun x _ => finiteConcentratingSlope_square S a ell hell hdisj x)]
  have hi (i : ℕ) (_hi : i∈S) : IntervalIntegrable
      (fun x => (concentratingIntervalIncrement (a i) ell x)^2) volume 0 1 :=
    ((lipschitz_concentratingIntervalIncrement (a i) ell hell).continuous.pow 2).intervalIntegrable 0 1
  rw [intervalIntegral.integral_finsetSum hi]
  have hEnergy (i : ℕ) (hi : i∈S) :
      (∫x in (0 : ℝ)..1,(concentratingIntervalIncrement (a i) ell x)^2)=512/(105*ell) := by
    rw [←deriv_concentratingIntervalBump]
    exact concentratingIntervalBump_unit_energy (a i) ell hell (ha i hi) (he i hi)
  rw [Finset.sum_congr rfl hEnergy]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

end QuantitativeFollowup
