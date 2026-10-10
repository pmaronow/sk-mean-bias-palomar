module
public import QuantitativeFollowup.FiniteConcentratingResponseTest
public import QuantitativeFollowup.ConcentratingMeasurePairing

@[expose] public section

/-! Genuine weighted area, atom-safe density and one-sign pairings for
finite disjoint concentrating tests. All integrability is derived from
actual continuous response functions and compact supports. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 2200000

theorem finiteConcentratingBump_zero_outside_unit (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0 < ell) (ha : ∀i∈S,0 ≤ a i) (he : ∀i∈S,a i+ell ≤ 1)
    (x : ℝ) (hx : x∉Ioc (0 : ℝ) 1) : finiteConcentratingBump S a ell x=0 := by
  apply finiteConcentratingBump_zero_outside S a ell hell
  intro hu
  obtain ⟨i,hi⟩ := mem_iUnion.mp hu
  obtain ⟨his,hxi⟩ := mem_iUnion.mp hi
  exact hx ⟨(ha i his).trans_lt hxi.1,hxi.2.le.trans (he i his)⟩

theorem finiteConcentratingBump_hasCompactSupport (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0 < ell) (ha : ∀i∈S,0 ≤ a i) (he : ∀i∈S,a i+ell ≤ 1) :
    HasCompactSupport (finiteConcentratingBump S a ell) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  intro x hx
  by_contra hn
  exact hx (finiteConcentratingBump_zero_outside_unit S a ell hell ha he x
    (fun hI => hn ⟨hI.1.le,hI.2⟩))

theorem finiteConcentrating_weighted_integrable (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0 < ell) (ha : ∀i∈S,0 ≤ a i) (he : ∀i∈S,a i+ell ≤ 1)
    (D : ℝ → ℝ) (hD : Continuous D) :
    Integrable (fun x=>D x*finiteConcentratingBump S a ell x) volume :=
  (hD.mul (continuous_finiteConcentratingBump S a ell)).integrable_of_hasCompactSupport
    ((finiteConcentratingBump_hasCompactSupport S a ell hell ha he).mul_left)

theorem finiteConcentrating_weighted_square_integrable (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0 < ell) (ha : ∀i∈S,0 ≤ a i) (he : ∀i∈S,a i+ell ≤ 1)
    (D : ℝ → ℝ) (hD : Continuous D) :
    Integrable (fun x=>D x*(finiteConcentratingBump S a ell x)^2) volume := by
  apply (hD.mul ((continuous_finiteConcentratingBump S a ell).pow 2)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  intro x hx
  by_contra hn
  apply hx
  change D x*(finiteConcentratingBump S a ell x)^2=0
  rw [finiteConcentratingBump_zero_outside_unit S a ell hell ha he x
    (fun hI => hn ⟨hI.1.le,hI.2⟩)]
  simp

theorem finiteConcentrating_weighted_mass_lower (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0 < ell) (ha : ∀i∈S,0 ≤ a i) (he : ∀i∈S,a i+ell ≤ 1)
    (D : ℝ → ℝ) (hD : Continuous D) (k : ℝ) (hk : 0 ≤ k)
    (hkD : ∀x∈Icc (0 : ℝ) 1,k ≤ D x) :
    k*(S.card : ℝ)*ell/2 ≤ ∫x in (0 : ℝ)..1,D x*finiteConcentratingBump S a ell x := by
  have hphi := continuous_finiteConcentratingBump S a ell
  have hh := intervalIntegral.integral_mono_on zero_le_one
    ((hphi.intervalIntegrable (μ:=volume) 0 1).const_mul k) ((hD.mul hphi).intervalIntegrable (μ:=volume) 0 1)
    (fun x hx=>mul_le_mul_of_nonneg_right (hkD x hx) (finiteConcentratingBump_nonneg S a ell x))
  rw [intervalIntegral.integral_const_mul,finiteConcentratingBump_unit_integral S a ell hell ha he] at hh
  simp only [Pi.mul_apply] at hh
  have hcard : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  nlinarith [mul_nonneg (mul_nonneg hk hcard) hell.le]

theorem finiteConcentrating_density_square_bound (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0 < ell) (ha : ∀i∈S,0 ≤ a i) (he : ∀i∈S,a i+ell ≤ 1)
    (hdisj : (S : Set ℕ).PairwiseDisjoint (fun i=>Ioo (a i) (a i+ell)))
    (D : ℝ → ℝ) (hD : Continuous D) (hDn : ∀x,0 ≤ D x)
    (eta : Measure ℝ) (q d : ℝ) (hd : 0 ≤ d)
    (hdensity : eta.restrict ({q}ᶜ) ≤ ENNReal.ofReal d • volume)
    (hzero : finiteConcentratingBump S a ell q=0) :
    (∫x : ℝ,D x*(finiteConcentratingBump S a ell x)^2 ∂eta) ≤
      d*(∫x in (0 : ℝ)..1,D x*finiteConcentratingBump S a ell x) := by
  have hi := finiteConcentrating_weighted_square_integrable S a ell hell ha he D hD
  have hnonneg : ∀x,0 ≤ D x*(finiteConcentratingBump S a ell x)^2 :=
    fun x=>mul_nonneg (hDn x) (sq_nonneg _)
  have heq : (∫x in {q}ᶜ,D x*(finiteConcentratingBump S a ell x)^2 ∂eta) =
      ∫x : ℝ,D x*(finiteConcentratingBump S a ell x)^2 ∂eta := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxq : x=q := by simpa only [mem_compl_iff,not_not,mem_singleton_iff] using hx
    subst x
    rw [hzero]
    simp
  rw [←heq]
  have hCompare := integral_mono_measure hdensity (.of_forall hnonneg)
    (hi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure,ENNReal.toReal_ofReal hd,smul_eq_mul] at hCompare
  have hSquare : (∫x : ℝ,D x*(finiteConcentratingBump S a ell x)^2) ≤
      ∫x : ℝ,D x*finiteConcentratingBump S a ell x := by
    apply integral_mono hi (finiteConcentrating_weighted_integrable S a ell hell ha he D hD)
    intro x
    have hp0 := finiteConcentratingBump_nonneg S a ell x
    have hp1 := finiteConcentratingBump_le_one S a ell hell hdisj x
    exact mul_le_mul_of_nonneg_left (by nlinarith :
      (finiteConcentratingBump S a ell x)^2 ≤ finiteConcentratingBump S a ell x) (hDn x)
  have hFull : (∫x in (0 : ℝ)..1,D x*finiteConcentratingBump S a ell x) =
      ∫x : ℝ,D x*finiteConcentratingBump S a ell x := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    by_contra hn
    apply hx
    change D x*finiteConcentratingBump S a ell x=0
    rw [finiteConcentratingBump_zero_outside_unit S a ell hell ha he x hn,mul_zero]
  rw [hFull]
  exact hCompare.trans (mul_le_mul_of_nonneg_left hSquare hd)

theorem finiteConcentrating_signed_pairing (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0 < ell) (D psi : ℝ → ℝ) (hD : Continuous D)
    (hDn : ∀x,0 ≤ D x) (A sigma : ℝ)
    (hSign : ∀i∈S,∀x∈Icc (a i) (a i+ell), A/2 ≤ sigma*psi x)
    (hi : IntervalIntegrable (fun x=>psi x*D x*finiteConcentratingBump S a ell x) volume 0 1) :
    A/2*(∫x in (0 : ℝ)..1,D x*finiteConcentratingBump S a ell x) ≤
      sigma*(∫x in (0 : ℝ)..1,psi x*D x*finiteConcentratingBump S a ell x) := by
  have hphi := continuous_finiteConcentratingBump S a ell
  have hPoint (x : ℝ) (_hx : x∈Icc (0 : ℝ) 1) :
      (A/2)*(D x*finiteConcentratingBump S a ell x) ≤
        sigma*(psi x*D x*finiteConcentratingBump S a ell x) := by
    by_cases hu : x∈⋃i∈S,Ioo (a i) (a i+ell)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hu
      obtain ⟨his,hxi⟩ := mem_iUnion.mp hi
      have hh := mul_le_mul_of_nonneg_right (hSign i his x ⟨hxi.1.le,hxi.2.le⟩)
        (mul_nonneg (hDn x) (finiteConcentratingBump_nonneg S a ell x))
      convert hh using 1
      ring
    · rw [finiteConcentratingBump_zero_outside S a ell hell x hu]
      simp
  have hh := intervalIntegral.integral_mono_on zero_le_one
    (((hD.mul hphi).intervalIntegrable (μ:=volume) 0 1).const_mul (A/2))
    (hi.const_mul sigma) hPoint
  simpa only [intervalIntegral.integral_const_mul,Pi.mul_apply] using hh

end QuantitativeFollowup
