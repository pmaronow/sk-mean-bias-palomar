module
public import QuantitativePaper.VectorRecursionIntegrability
public import QuantitativePaper.ScalarVariational

@[expose] public section

/-! Exact physical endpoint identities for the finite-profile, finite-N
interpolating functional built from the actual vector Gaussian recursion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

def finiteVectorFunctional {k : ℕ} (n : ℕ) (s : RSBScheme k) (β t a : ℝ) : ℝ :=
  Real.log (∫ p,Real.exp (a*vectorRecursion s β t p (k+2) 0) ∂completionLaw n)/((n:ℝ)*a)-
    (1-t)*(β^2/2*∫ q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q)

theorem finiteVectorFunctional_zero (n : ℕ) (hn : 0 < n) {k : ℕ} (s : RSBScheme k)
    (β a : ℝ) (ha : a ≠ 0) :
    finiteVectorFunctional n s β 0 a = parisiFunctional s β 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold finiteVectorFunctional
  simp_rw [vectorRecursion_zero_time]
  simp only [PiLp.zero_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    integral_const,probReal_univ,one_smul,Real.log_exp,sub_zero,one_mul]
  rw [Paper.parisiScheme_correction_eq]
  unfold parisiFunctional
  field_simp

theorem finiteVectorFunctional_zero_actual (n : ℕ) (hn : 0 < n) {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (a : ℝ) (ha : a ≠ 0) :
    finiteVectorFunctional n s β 0 a = scalarParisiFunctional β (Paper.parisiSchemeMeasure s) := by
  rw [finiteVectorFunctional_zero n hn s β a ha]
  exact (Paper.parisiPDEFunctional_scheme s β hβ 0).symm

theorem finiteVectorFunctional_one (n : ℕ) {k : ℕ} (s : RSBScheme k)
    (β a : ℝ) (ha : a ≠ 0) :
    finiteVectorFunctional n s β 1 a = completedFractionalPressure n β a := by
  unfold finiteVectorFunctional completedFractionalPressure
  rw [ite_eq_right ha]
  simp_rw [vectorRecursion_one_time,vectorTerminalPotential_one_time_zero]
  simp only [sub_self,zero_mul,sub_zero]
  rfl

end QuantitativePaper
