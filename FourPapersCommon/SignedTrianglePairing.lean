module
public import FourPapersCommon.WeightedTriangleCutoff

@[expose] public section

/-! Both actual signs of the triangular cutoff pairing. No regularity
of the discrepancy beyond the displayed integral's integrability is
needed for the deterministic one-sign estimate. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
set_option maxHeartbeats 1200000

theorem finiteTriangleCutoff_negative_pairing (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0<ell) (A : ℝ) (zeta psi : ℝ → ℝ)
    (hz : ∀x∈Icc (0 : ℝ) 1, 0≤zeta x)
    (hpsi : ∀i∈S, ∀x∈Icc (a i) (a i+ell), psi x≤ -A/2)
    (hi : IntervalIntegrable (fun x => zeta x*finiteTriangleCutoff S a ell x) volume 0 1)
    (hip : IntervalIntegrable (fun x => psi x*zeta x*finiteTriangleCutoff S a ell x) volume 0 1) :
    A/2*(∫x in (0 : ℝ)..1, zeta x*finiteTriangleCutoff S a ell x) ≤
      |∫x in (0 : ℝ)..1, psi x*zeta x*finiteTriangleCutoff S a ell x| := by
  have hin : IntervalIntegrable (fun x => (-psi x)*zeta x*finiteTriangleCutoff S a ell x) volume 0 1 := by
    convert hip.neg using 1
    funext x
    simp only [neg_mul,Pi.neg_apply]
  have hh := finiteTriangleCutoff_positive_pairing S a ell hell A zeta (fun x => -psi x)
    hz (fun i hi x hx => by linarith [hpsi i hi x hx]) hi hin
  simpa only [neg_mul,intervalIntegral.integral_neg,abs_neg] using hh

theorem finiteTriangleCutoff_signed_pairing (S : Finset ℕ) (a : ℕ → ℝ)
    (ell : ℝ) (hell : 0<ell) (A sigma : ℝ) (hsigma : |sigma|=1)
    (zeta psi : ℝ → ℝ) (hz : ∀x∈Icc (0 : ℝ) 1, 0≤zeta x)
    (hpsi : ∀i∈S, ∀x∈Icc (a i) (a i+ell), A/2≤sigma*psi x)
    (hi : IntervalIntegrable (fun x => zeta x*finiteTriangleCutoff S a ell x) volume 0 1)
    (hip : IntervalIntegrable (fun x => psi x*zeta x*finiteTriangleCutoff S a ell x) volume 0 1) :
    A/2*(∫x in (0 : ℝ)..1, zeta x*finiteTriangleCutoff S a ell x) ≤
      |∫x in (0 : ℝ)..1, psi x*zeta x*finiteTriangleCutoff S a ell x| := by
  have his : IntervalIntegrable (fun x => (sigma*psi x)*zeta x*finiteTriangleCutoff S a ell x) volume 0 1 := by
    simpa only [mul_assoc] using hip.const_mul sigma
  have hh := finiteTriangleCutoff_positive_pairing S a ell hell A zeta (fun x => sigma*psi x)
    hz hpsi hi his
  have he : (fun x => (sigma*psi x)*zeta x*finiteTriangleCutoff S a ell x) =
      (fun x => sigma*(psi x*zeta x*finiteTriangleCutoff S a ell x)) := by funext x; ring
  rw [he,intervalIntegral.integral_const_mul,abs_mul,hsigma,one_mul] at hh
  exact hh

end FourPapersCommon
