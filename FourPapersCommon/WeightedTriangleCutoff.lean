module
public import FourPapersCommon.FiniteTriangleSupport
public import FourPapersCommon.ResponseCoercivity

@[expose] public section

/-! Literal weighted mass, weighted Dirichlet energy, and one-sign
pairing estimates for the constructed triangular tests. The response
estimate remains an explicit analytic input, separate from these integral
and geometric facts. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1800000

theorem finiteTriangleCutoff_weighted_integrable (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0 < ell)
    (hdisj : (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (a i) (a i + ell)))
    (zeta : ℝ → ℝ) (hzm : Measurable zeta) (U : ℝ)
    (hz : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ zeta x ∧ zeta x ≤ U) :
    IntervalIntegrable (fun x => zeta x * finiteTriangleCutoff S a ell x) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  apply Integrable.of_bound (hzm.mul
    (finiteTriangleCutoff_lipschitz S a ell hell).continuous.measurable).aestronglyMeasurable U
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  change ‖zeta x * finiteTriangleCutoff S a ell x‖ ≤ U
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hz x hx).1
    (finiteTriangleCutoff_nonneg S a ell x))]
  exact (mul_le_mul_of_nonneg_left (finiteTriangleCutoff_le_one S a ell hell hdisj x)
    (hz x hx).1).trans (by simpa only [mul_one] using (hz x hx).2)

theorem finiteTriangleCutoff_weighted_mass_bounds (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0 < ell) (ha : ∀ i ∈ S, 0 ≤ a i)
    (he : ∀ i ∈ S, a i + ell ≤ 1)
    (hdisj : (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (a i) (a i + ell)))
    (zeta : ℝ → ℝ) (hzm : Measurable zeta) (k U : ℝ) (hk : 0 ≤ k)
    (hz : ∀ x ∈ Icc (0 : ℝ) 1, k ≤ zeta x ∧ zeta x ≤ U) :
    k * (S.card * ell / 2) ≤ (∫ x in (0 : ℝ)..1, zeta x * finiteTriangleCutoff S a ell x) ∧
      (∫ x in (0 : ℝ)..1, zeta x * finiteTriangleCutoff S a ell x) ≤ U * (S.card * ell / 2) := by
  have hi := finiteTriangleCutoff_weighted_integrable S a ell hell hdisj zeta hzm U
    (fun x hx => ⟨hk.trans (hz x hx).1, (hz x hx).2⟩)
  have hip := (finiteTriangleCutoff_lipschitz S a ell hell).continuous.intervalIntegrable
    (μ := volume) 0 1
  have hlo := intervalIntegral.integral_mono_on zero_le_one (hip.const_mul k) hi
    (fun x hx => mul_le_mul_of_nonneg_right (hz x hx).1 (finiteTriangleCutoff_nonneg S a ell x))
  have hup := intervalIntegral.integral_mono_on zero_le_one hi (hip.const_mul U)
    (fun x hx => mul_le_mul_of_nonneg_right (hz x hx).2 (finiteTriangleCutoff_nonneg S a ell x))
  rw [intervalIntegral.integral_const_mul, finiteTriangleCutoff_integral_unit S a ell hell ha he] at hlo hup
  exact ⟨hlo, hup⟩

theorem finiteTriangleCutoff_weighted_energy_integrable (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0 < ell) (zeta : ℝ → ℝ) (hzm : Measurable zeta) (U : ℝ)
    (hz : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ zeta x ∧ zeta x ≤ U) :
    IntervalIntegrable (fun x => zeta x * (deriv (finiteTriangleCutoff S a ell) x) ^ 2) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  apply Integrable.of_bound (hzm.mul ((measurable_deriv _).pow_const 2)).aestronglyMeasurable
    (U * ((S.card : ℝ) * (2 / ell)) ^ 2)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  change ‖zeta x*(deriv (finiteTriangleCutoff S a ell) x)^2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hz x hx).1 (sq_nonneg _))]
  have hd := norm_deriv_le_of_lipschitz (x₀ := x) (finiteTriangleCutoff_lipschitz S a ell hell)
  rw [Real.coe_toNNReal _ (by positivity)] at hd
  have hd2 : (deriv (finiteTriangleCutoff S a ell) x)^2 ≤ ((S.card : ℝ)*(2/ell))^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hU : 0 ≤ U := (hz x hx).1.trans (hz x hx).2
  exact mul_le_mul (hz x hx).2 hd2 (sq_nonneg _) hU

theorem finiteTriangleCutoff_weighted_energy_bounds (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0 < ell) (ha : ∀ i ∈ S, 0 ≤ a i)
    (he : ∀ i ∈ S, a i + ell ≤ 1)
    (hdisj : (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (a i) (a i + ell)))
    (zeta : ℝ → ℝ) (hzm : Measurable zeta) (U : ℝ)
    (hz : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ zeta x ∧ zeta x ≤ U) :
    0 ≤ (∫ x in (0 : ℝ)..1, zeta x * (deriv (finiteTriangleCutoff S a ell) x)^2) ∧
      (∫ x in (0 : ℝ)..1, zeta x * (deriv (finiteTriangleCutoff S a ell) x)^2) ≤
        U * (4*S.card/ell) := by
  have hi := finiteTriangleCutoff_weighted_energy_integrable S a ell hell zeta hzm U hz
  have hip : IntervalIntegrable (fun x => (deriv (finiteTriangleCutoff S a ell) x)^2) volume 0 1 := by
    have hsum := IntervalIntegrable.sum S (fun i (_ : i ∈ S) =>
      triangleCutoff_energy_intervalIntegrable (a i) ell hell)
    have hsum' : IntervalIntegrable
        (fun x => ∑ i ∈ S, (deriv (triangleCutoff (a i) ell) x)^2) volume 0 1 := by
      simpa only [Finset.sum_fn] using hsum
    exact hsum'.congr_ae (ae_restrict_of_ae (finiteTriangleCutoff_deriv_sq_ae S a ell hell hdisj).symm)
  refine ⟨intervalIntegral.integral_nonneg zero_le_one
    (fun x hx => mul_nonneg (hz x hx).1 (sq_nonneg _)), ?_⟩
  have hup := intervalIntegral.integral_mono_on zero_le_one hi (hip.const_mul U)
      (fun x hx => mul_le_mul_of_nonneg_right (hz x hx).2 (sq_nonneg _))
  rw [intervalIntegral.integral_const_mul, finiteTriangleCutoff_energy_unit S a ell hell ha he hdisj] at hup
  exact hup

/-- A positive one-sign test pairs at least its weighted mass times A/2.
The sign requirement is only on the constructed support intervals. -/
theorem finiteTriangleCutoff_positive_pairing (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0 < ell) (A : ℝ) (zeta psi : ℝ → ℝ)
    (hz : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ zeta x)
    (hpsi : ∀ i ∈ S, ∀ x ∈ Icc (a i) (a i + ell), A / 2 ≤ psi x)
    (hi : IntervalIntegrable (fun x => zeta x * finiteTriangleCutoff S a ell x) volume 0 1)
    (hip : IntervalIntegrable (fun x => psi x*zeta x*finiteTriangleCutoff S a ell x) volume 0 1) :
    A/2 * (∫ x in (0 : ℝ)..1, zeta x*finiteTriangleCutoff S a ell x) ≤
      |∫ x in (0 : ℝ)..1, psi x*zeta x*finiteTriangleCutoff S a ell x| := by
  have hp (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      (A/2)*(zeta x*finiteTriangleCutoff S a ell x) ≤
        psi x*zeta x*finiteTriangleCutoff S a ell x := by
    by_cases hu : x ∈ ⋃ i ∈ S, Ioo (a i) (a i+ell)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hu
      obtain ⟨his, hxi⟩ := mem_iUnion.mp hi
      have hh := mul_le_mul_of_nonneg_right (hpsi i his x ⟨hxi.1.le, hxi.2.le⟩)
        (mul_nonneg (hz x hx) (finiteTriangleCutoff_nonneg S a ell x))
      convert hh using 1; ring
    · rw [finiteTriangleCutoff_zero_outside S a ell hell x hu]
      simp
  have hh := intervalIntegral.integral_mono_on zero_le_one (hi.const_mul (A/2)) hip hp
  rw [intervalIntegral.integral_const_mul] at hh
  exact hh.trans (le_abs_self _)

end FourPapersCommon
