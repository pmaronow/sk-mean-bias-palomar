module
public import FourPapersCommon.TriangleCutoffEnergy

@[expose] public section

/-! A constructed finite disjoint family of triangular cutoffs, with
literal total area and Dirichlet energy. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1500000

def finiteTriangleCutoff (S : Finset ℕ) (a : ℕ → ℝ) (ell x : ℝ) : ℝ :=
  ∑ i ∈ S, triangleCutoff (a i) ell x

theorem finiteTriangleCutoff_nonneg (S : Finset ℕ) (a : ℕ → ℝ) (ell x : ℝ) :
    0 ≤ finiteTriangleCutoff S a ell x :=
  Finset.sum_nonneg (fun i _ => triangleCutoff_nonneg (a i) ell x)

theorem finiteTriangleCutoff_zero_outside (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell) (x : ℝ) (hx : x ∉ ⋃ i ∈ S, Ioo (a i) (a i + ell)) :
    finiteTriangleCutoff S a ell x = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact triangleCutoff_zero_outside (a i) ell x hell
    (fun h => hx (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, h⟩⟩))

theorem finiteTriangleCutoff_le_one (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell)
    (hdisj : (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (a i) (a i + ell))) (x : ℝ) :
    finiteTriangleCutoff S a ell x ≤ 1 := by
  classical
  by_cases hx : ∃ i ∈ S, x ∈ Ioo (a i) (a i + ell)
  · obtain ⟨i, hi, hxi⟩ := hx
    have he : finiteTriangleCutoff S a ell x = triangleCutoff (a i) ell x := by
      apply Finset.sum_eq_single_of_mem i hi
      intro j hj hji
      exact triangleCutoff_zero_outside (a j) ell x hell
        (fun hxj => (Set.disjoint_left.mp (hdisj hi hj hji.symm)) hxi hxj)
    rw [he]
    exact triangleCutoff_le_one (a i) ell x hell
  · have hxu : x ∉ ⋃ i ∈ S, Ioo (a i) (a i + ell) := by
      intro hu
      obtain ⟨i, hi⟩ := mem_iUnion.mp hu
      obtain ⟨his, hxi⟩ := mem_iUnion.mp hi
      exact hx ⟨i, his, hxi⟩
    rw [finiteTriangleCutoff_zero_outside S a ell hell x hxu]
    norm_num

theorem finiteTriangleCutoff_lipschitz (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ) (hell : 0 < ell) :
    LipschitzWith (Real.toNNReal ((S.card : ℝ) * (2 / ell))) (finiteTriangleCutoff S a ell) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  have hb (i : ℕ) : |triangleCutoff (a i) ell x - triangleCutoff (a i) ell y| ≤
      (2 / ell) * |x - y| := by
    have hi := (triangleCutoff_lipschitz (a i) ell hell).dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at hi
    exact hi
  calc
    _ = |∑ i ∈ S, (triangleCutoff (a i) ell x - triangleCutoff (a i) ell y)| := by
      rw [Finset.sum_sub_distrib]
      rfl
    _ ≤ ∑ i ∈ S, |triangleCutoff (a i) ell x - triangleCutoff (a i) ell y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, (2 / ell) * |x - y| := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem finiteTriangleCutoff_integral_unit (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell) (ha : ∀ i ∈ S, 0 ≤ a i) (he : ∀ i ∈ S, a i + ell ≤ 1) :
    (∫ x in (0 : ℝ)..1, finiteTriangleCutoff S a ell x) = S.card * ell / 2 := by
  unfold finiteTriangleCutoff
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_triangleCutoff (a i) ell hell).intervalIntegrable 0 1)]
  have hv : ∀ i ∈ S, (∫ x in (0 : ℝ)..1, triangleCutoff (a i) ell x) = ell / 2 :=
    fun i hi => triangleCutoff_integral_unit (a i) ell hell (ha i hi) (he i hi)
  rw [Finset.sum_congr rfl hv]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem sq_sum_of_pairwise_products_zero (S : Finset ℕ) (d : ℕ → ℝ)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → d i * d j = 0) :
    (∑ i ∈ S, d i) ^ 2 = ∑ i ∈ S, (d i) ^ 2 := by
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem i hi
    (fun j hj hji => hd i hi j hj hji.symm)]
  exact (pow_two (d i)).symm

theorem finiteTriangleCutoff_deriv_sq_ae (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell)
    (hdisj : (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (a i) (a i + ell))) :
    (fun x => (deriv (finiteTriangleCutoff S a ell) x) ^ 2) =ᵐ[volume]
      (fun x => ∑ i ∈ S, (deriv (triangleCutoff (a i) ell) x) ^ 2) := by
  have hDiff : ∀ᵐ x ∂ volume, ∀ i : ℕ, DifferentiableAt ℝ (triangleCutoff (a i) ell) x :=
    ae_all_iff.mpr (fun i => ae_differentiableAt_triangleCutoff (a i) ell hell)
  have hSquare : ∀ᵐ x ∂ volume, ∀ i : ℕ,
      (deriv (triangleCutoff (a i) ell) x) ^ 2 =
        (Ioo (a i) (a i + ell)).indicator (fun _ : ℝ => (2 / ell) ^ 2) x :=
    ae_all_iff.mpr (fun i => deriv_triangleCutoff_sq_ae (a i) ell hell)
  filter_upwards [hDiff, hSquare] with x hx hs
  have he := deriv_fun_sum (u := S) (fun i _ => hx i)
  change deriv (finiteTriangleCutoff S a ell) x =
    ∑ i ∈ S, deriv (triangleCutoff (a i) ell) x at he
  rw [he]
  apply sq_sum_of_pairwise_products_zero
  intro i hi j hj hij
  by_cases hxi : x ∈ Ioo (a i) (a i + ell)
  · have hxj : x ∉ Ioo (a j) (a j + ell) :=
      fun hxj => (Set.disjoint_left.mp (hdisj hi hj hij)) hxi hxj
    have hjz : deriv (triangleCutoff (a j) ell) x = 0 := by
      have hh := hs j
      rw [indicator_of_notMem hxj] at hh
      exact sq_eq_zero_iff.mp hh
    rw [hjz, mul_zero]
  · have hiz : deriv (triangleCutoff (a i) ell) x = 0 := by
      have hh := hs i
      rw [indicator_of_notMem hxi] at hh
      exact sq_eq_zero_iff.mp hh
    rw [hiz, zero_mul]

theorem finiteTriangleCutoff_energy_unit (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell) (ha : ∀ i ∈ S, 0 ≤ a i) (he : ∀ i ∈ S, a i + ell ≤ 1)
    (hdisj : (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (a i) (a i + ell))) :
    (∫ x in (0 : ℝ)..1, (deriv (finiteTriangleCutoff S a ell) x) ^ 2) = 4 * S.card / ell := by
  rw [intervalIntegral.integral_congr_ae_restrict
    (ae_restrict_of_ae (finiteTriangleCutoff_deriv_sq_ae S a ell hell hdisj))]
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    triangleCutoff_energy_intervalIntegrable (a i) ell hell)]
  have hv : ∀ i ∈ S, (∫ x in (0 : ℝ)..1, (deriv (triangleCutoff (a i) ell) x) ^ 2) = 4 / ell :=
    fun i hi => triangleCutoff_energy_unit (a i) ell hell (ha i hi) (he i hi)
  rw [Finset.sum_congr rfl hv]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

end FourPapersCommon
