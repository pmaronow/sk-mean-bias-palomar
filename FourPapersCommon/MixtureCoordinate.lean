module
public import FourPapersCommon.MixtureAnalysis

@[expose] public section

/-! Genuine single interaction-amplitude perturbations of an exponentially
summable covariance. The parameter is the manuscript's b_p, rather than
its square, and all other independent-interaction coefficients are fixed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FourPapersCommon.AdmissibleEvenMixture
set_option maxHeartbeats 800000

theorem ext_coefficient {ξ η : AdmissibleEvenMixture}
    (h : ξ.coefficient = η.coefficient) : ξ = η := by
  cases ξ
  cases η
  cases h
  rfl

def amplitudeCoordinate (ξ : AdmissibleEvenMixture) (p : ℕ) (hp : 2 ≤ p ∧ Even p)
    (a : {a : ℝ // 0 < a}) : AdmissibleEvenMixture where
  coefficient := Function.update ξ.coefficient p ((a : ℝ) ^ 2)
  nonneg := fun n => by
    by_cases hn : n = p
    · simp only [hn, Function.update_self]
      exact sq_nonneg _
    · rw [Function.update_of_ne hn]
      exact ξ.nonneg n
  active_even := fun n hn => by
    by_cases he : n = p
    · simpa only [he] using hp
    · exact ξ.active_even n (by simpa only [Function.update_of_ne he] using hn)
  nonzero := ⟨p, by simpa only [Function.update_self] using sq_pos_of_pos a.property⟩
  summable := by
    have he : (fun n : ℕ => (2 : ℝ) ^ n * Function.update ξ.coefficient p ((a : ℝ) ^ 2) n) =
        Function.update (fun n : ℕ => (2 : ℝ) ^ n * ξ.coefficient n) p ((2 : ℝ) ^ p * (a : ℝ) ^ 2) := by
      funext n
      by_cases hn : n = p <;> simp [hn, Function.update_of_ne]
    rw [he]
    exact ξ.summable.update p _

@[simp] theorem amplitudeCoordinate_coefficient_self (ξ : AdmissibleEvenMixture)
    (p : ℕ) (hp : 2 ≤ p ∧ Even p) (a : {a : ℝ // 0 < a}) :
    (ξ.amplitudeCoordinate p hp a).coefficient p = (a : ℝ) ^ 2 := by
  simp [amplitudeCoordinate]

theorem amplitudeCoordinate_coefficient_other (ξ : AdmissibleEvenMixture)
    (p : ℕ) (hp : 2 ≤ p ∧ Even p) (a : {a : ℝ // 0 < a}) {n : ℕ} (hn : n ≠ p) :
    (ξ.amplitudeCoordinate p hp a).coefficient n = ξ.coefficient n := by
  simp [amplitudeCoordinate, hn]

private theorem tsum_weighted_update (c w : ℕ → ℝ) (p : ℕ) (a : ℝ)
    (hc : Summable (fun n => w n * c n)) :
    (∑' n, w n * Function.update c p a n) = (∑' n, w n * c n) + (a - c p) * w p := by
  have he : (fun n => w n * Function.update c p a n) =
      Function.update (fun n => w n * c n) p (w p * a) := by
    funext n
    by_cases hn : n = p <;> simp [hn, Function.update_of_ne]
  rw [he, (hc.hasSum.update p (w p * a)).tsum_eq]
  ring

theorem amplitudeCoordinate_value (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2 ≤ p ∧ Even p) (a : {a : ℝ // 0 < a}) {q : ℝ} (hq : |q| ≤ 1) :
    (ξ.amplitudeCoordinate p hp a).value q =
      ξ.value q + ((a : ℝ) ^ 2 - ξ.coefficient p) * q ^ p := by
  have hs : Summable (fun n => q ^ n * ξ.coefficient n) := by
    simpa only [mul_comm] using ξ.summable_value hq
  simpa only [amplitudeCoordinate, value, mul_comm] using
    tsum_weighted_update ξ.coefficient (fun n => q ^ n) p ((a : ℝ) ^ 2) hs

theorem amplitudeCoordinate_first (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2 ≤ p ∧ Even p) (a : {a : ℝ // 0 < a}) {q : ℝ} (hq : |q| ≤ 1) :
    (ξ.amplitudeCoordinate p hp a).first q =
      ξ.first q + ((a : ℝ) ^ 2 - ξ.coefficient p) * (p : ℝ) * q ^ (p - 1) := by
  have hs : Summable (fun n : ℕ => ((n : ℝ) * q ^ (n - 1)) * ξ.coefficient n) := by
    convert ξ.summable_first hq using 1
    funext n
    ring
  have H := tsum_weighted_update ξ.coefficient (fun n : ℕ => (n : ℝ) * q ^ (n - 1))
    p ((a : ℝ) ^ 2) hs
  have he : (∑' n : ℕ, ((n : ℝ) * q ^ (n - 1)) * ξ.coefficient n) = ξ.first q := by
    unfold first
    apply tsum_congr
    intro n
    ring
  rw [he] at H
  calc
    _ = ∑' n : ℕ, ((n : ℝ) * q ^ (n - 1)) * Function.update ξ.coefficient p ((a : ℝ) ^ 2) n := by
      apply tsum_congr
      intro n
      change (n : ℝ) * Function.update ξ.coefficient p ((a : ℝ) ^ 2) n * q ^ (n - 1) = _
      ring
    _ = _ := H.trans (by ring)

theorem amplitudeCoordinate_second (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2 ≤ p ∧ Even p) (a : {a : ℝ // 0 < a}) {q : ℝ} (hq : |q| ≤ 1) :
    (ξ.amplitudeCoordinate p hp a).second q =
      ξ.second q + ((a : ℝ) ^ 2 - ξ.coefficient p) * (p : ℝ) * (p - 1 : ℕ) * q ^ (p - 2) := by
  have hs : Summable (fun n : ℕ => ((n : ℝ) * (n - 1 : ℕ) * q ^ (n - 2)) * ξ.coefficient n) := by
    convert ξ.summable_second hq using 1
    funext n
    ring
  have H := tsum_weighted_update ξ.coefficient
    (fun n : ℕ => (n : ℝ) * (n - 1 : ℕ) * q ^ (n - 2)) p ((a : ℝ) ^ 2) hs
  have he : (∑' n : ℕ, ((n : ℝ) * (n - 1 : ℕ) * q ^ (n - 2)) * ξ.coefficient n) = ξ.second q := by
    unfold second
    apply tsum_congr
    intro n
    ring
  rw [he] at H
  calc
    _ = ∑' n : ℕ, ((n : ℝ) * (n - 1 : ℕ) * q ^ (n - 2)) * Function.update ξ.coefficient p ((a : ℝ) ^ 2) n := by
      apply tsum_congr
      intro n
      change (n : ℝ) * (n - 1 : ℕ) * Function.update ξ.coefficient p ((a : ℝ) ^ 2) n * q ^ (n - 2) = _
      ring
    _ = _ := H.trans (by ring)

theorem amplitudeCoordinate_variance (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2 ≤ p ∧ Even p) (a : {a : ℝ // 0 < a}) :
    (ξ.amplitudeCoordinate p hp a).variance = ξ.variance +
      ((a : ℝ) ^ 2 - ξ.coefficient p) * (p : ℝ) := by
  simpa only [variance, one_pow, mul_one] using ξ.amplitudeCoordinate_first p hp a (by norm_num : |(1 : ℝ)| ≤ 1)

def amplitudeCurve (ξ : AdmissibleEvenMixture) (p : ℕ) (hp : 2 ≤ p ∧ Even p)
    (a : ℝ) : AdmissibleEvenMixture :=
  if ha : 0 < a then ξ.amplitudeCoordinate p hp ⟨a, ha⟩ else ξ

theorem amplitudeCurve_of_pos (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2 ≤ p ∧ Even p) {a : ℝ} (ha : 0 < a) :
    ξ.amplitudeCurve p hp a = ξ.amplitudeCoordinate p hp ⟨a, ha⟩ := dif_pos ha

theorem amplitudeCoordinate_base (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2 ≤ p ∧ Even p) (hactive : 0 < ξ.coefficient p) :
    ξ.amplitudeCoordinate p hp ⟨Real.sqrt (ξ.coefficient p), Real.sqrt_pos.mpr hactive⟩ = ξ := by
  apply ext_coefficient
  funext n
  by_cases hn : n = p
  · subst n
    simp only [amplitudeCoordinate_coefficient_self, Real.sq_sqrt (ξ.nonneg p)]
  · exact ξ.amplitudeCoordinate_coefficient_other p hp _ hn

theorem amplitudeCurve_base (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2 ≤ p ∧ Even p) (hactive : 0 < ξ.coefficient p) :
    ξ.amplitudeCurve p hp (Real.sqrt (ξ.coefficient p)) = ξ := by
  rw [ξ.amplitudeCurve_of_pos p hp (Real.sqrt_pos.mpr hactive)]
  exact ξ.amplitudeCoordinate_base p hp hactive

theorem amplitudeCoordinate_first_sub_bound (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2 ≤ p ∧ Even p) (a b : {a : ℝ // 0 < a}) {q : ℝ} (hq : |q| ≤ 1) :
    |(ξ.amplitudeCoordinate p hp a).first q - (ξ.amplitudeCoordinate p hp b).first q| ≤
      (p : ℝ) * |(a : ℝ) ^ 2 - (b : ℝ) ^ 2| := by
  rw [ξ.amplitudeCoordinate_first p hp a hq, ξ.amplitudeCoordinate_first p hp b hq,
    show ξ.first q + ((a : ℝ) ^ 2 - ξ.coefficient p) * (p : ℝ) * q ^ (p - 1) -
      (ξ.first q + ((b : ℝ) ^ 2 - ξ.coefficient p) * (p : ℝ) * q ^ (p - 1)) =
      (p : ℝ) * ((a : ℝ) ^ 2 - (b : ℝ) ^ 2) * q ^ (p - 1) by ring,
    abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg p), abs_pow]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ (n := p - 1) (abs_nonneg q) hq)
    (mul_nonneg (Nat.cast_nonneg p) (abs_nonneg ((a : ℝ) ^ 2 - (b : ℝ) ^ 2)))

theorem amplitudeCoordinate_second_sub_bound (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2 ≤ p ∧ Even p) (a b : {a : ℝ // 0 < a}) {q : ℝ} (hq : |q| ≤ 1) :
    |(ξ.amplitudeCoordinate p hp a).second q - (ξ.amplitudeCoordinate p hp b).second q| ≤
      (p : ℝ) * (p - 1 : ℕ) * |(a : ℝ) ^ 2 - (b : ℝ) ^ 2| := by
  rw [ξ.amplitudeCoordinate_second p hp a hq, ξ.amplitudeCoordinate_second p hp b hq,
    show ξ.second q + ((a : ℝ) ^ 2 - ξ.coefficient p) * (p : ℝ) * (p - 1 : ℕ) * q ^ (p - 2) -
      (ξ.second q + ((b : ℝ) ^ 2 - ξ.coefficient p) * (p : ℝ) * (p - 1 : ℕ) * q ^ (p - 2)) =
      (p : ℝ) * (p - 1 : ℕ) * ((a : ℝ) ^ 2 - (b : ℝ) ^ 2) * q ^ (p - 2) by ring,
    abs_mul, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg p),
    abs_of_nonneg (Nat.cast_nonneg (p - 1)), abs_pow]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ (n := p - 2) (abs_nonneg q) hq)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg (p - 1)))
      (abs_nonneg ((a : ℝ) ^ 2 - (b : ℝ) ^ 2)))

theorem hasDerivAt_amplitudeCurve_value (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2 ≤ p ∧ Even p) {a q : ℝ} (ha : 0 < a) (hq : |q| ≤ 1) :
    HasDerivAt (fun b => (ξ.amplitudeCurve p hp b).value q) (2 * a * q ^ p) a := by
  have hd : HasDerivAt (fun b : ℝ => ξ.value q + (b ^ 2 - ξ.coefficient p) * q ^ p)
      (2 * a * q ^ p) a := by
    convert (((hasDerivAt_id a).pow 2).sub_const (ξ.coefficient p)).mul_const (q ^ p) |>.const_add (ξ.value q) using 1 <;> simp
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with b hb
  rw [ξ.amplitudeCurve_of_pos p hp hb]
  exact ξ.amplitudeCoordinate_value p hp ⟨b, hb⟩ hq

theorem hasDerivAt_amplitudeCurve_first (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2 ≤ p ∧ Even p) {a q : ℝ} (ha : 0 < a) (hq : |q| ≤ 1) :
    HasDerivAt (fun b => (ξ.amplitudeCurve p hp b).first q)
      (2 * a * (p : ℝ) * q ^ (p - 1)) a := by
  have hd : HasDerivAt (fun b : ℝ => ξ.first q + (b ^ 2 - ξ.coefficient p) * (p : ℝ) * q ^ (p - 1))
      (2 * a * (p : ℝ) * q ^ (p - 1)) a := by
    convert ((((hasDerivAt_id a).pow 2).sub_const (ξ.coefficient p)).mul_const (p : ℝ)).mul_const (q ^ (p - 1)) |>.const_add (ξ.first q) using 1 <;> simp
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with b hb
  rw [ξ.amplitudeCurve_of_pos p hp hb]
  exact ξ.amplitudeCoordinate_first p hp ⟨b, hb⟩ hq

theorem hasDerivAt_amplitudeCurve_second (ξ : AdmissibleEvenMixture) (p : ℕ)
    (hp : 2 ≤ p ∧ Even p) {a q : ℝ} (ha : 0 < a) (hq : |q| ≤ 1) :
    HasDerivAt (fun b => (ξ.amplitudeCurve p hp b).second q)
      (2 * a * (p : ℝ) * (p - 1 : ℕ) * q ^ (p - 2)) a := by
  have hd : HasDerivAt (fun b : ℝ => ξ.second q + (b ^ 2 - ξ.coefficient p) * (p : ℝ) * (p - 1 : ℕ) * q ^ (p - 2))
      (2 * a * (p : ℝ) * (p - 1 : ℕ) * q ^ (p - 2)) a := by
    convert (((((hasDerivAt_id a).pow 2).sub_const (ξ.coefficient p)).mul_const (p : ℝ)).mul_const (p - 1 : ℕ)).mul_const (q ^ (p - 2)) |>.const_add (ξ.second q) using 1 <;> simp
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with b hb
  rw [ξ.amplitudeCurve_of_pos p hp hb]
  exact ξ.amplitudeCoordinate_second p hp ⟨b, hb⟩ hq

end FourPapersCommon.AdmissibleEvenMixture
