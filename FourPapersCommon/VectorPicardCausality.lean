module
public import FourPapersCommon.VectorPicardMeasurable

@[expose] public section

/-! Causality of the constructed integral solution: the solution up to a time
uses only the drift up to that time. This is proved from integral-equation
uniqueness, and does not assert causality as a hypothesis. -/
noncomputable section
open Function MeasureTheory Set
open scoped NNReal
namespace FourPapersCommon.VectorIntegralPicard
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) {x0 : E} {L K : ℝ≥0}
  {f g : ℝ → E → E}

theorem solution_compProj_equation (hf : IsBoundedVectorDrift f L K)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    (solution (h := x0) hT hf).compProj r = x0 +
      ∫ s in 0..r,f s ((solution (h := x0) hT hf).compProj s) := by
  rw [ODE.FunSpace.compProj_of_mem hr]
  exact solution_equation hT hf ⟨r,hr⟩

include hS in
theorem solution_causal (hST : S ≤ T)
    (hf : IsBoundedVectorDrift f L K) (hg : IsBoundedVectorDrift g L K)
    (hfg : ∀ r ∈ Icc (0 : ℝ) S,∀ x,f r x = g r x) :
    ∀ r ∈ Icc (0 : ℝ) S,
      (solution (h := x0) hT hf).compProj r =
      (solution (h := x0) hT hg).compProj r := by
  have hfirst := real_solution_unique (h := x0) hS hf
    (fun r => (solution (h := x0) hT hf).compProj r)
    (ODE.FunSpace.continuous_compProj _) (fun r hr =>
      solution_compProj_equation hT hf ⟨hr.1,hr.2.trans hST⟩)
  have hsecond := real_solution_unique (h := x0) hS hf
    (fun r => (solution (h := x0) hT hg).compProj r)
    (ODE.FunSpace.continuous_compProj _) (by
      intro r hr
      rw [solution_compProj_equation hT hg ⟨hr.1,hr.2.trans hST⟩]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hr.1] at hs
      exact (hfg s ⟨hs.1,hs.2.trans hr.2⟩ _).symm)
  intro r hr
  exact (hfirst r hr).trans (hsecond r hr).symm

end FourPapersCommon.VectorIntegralPicard
