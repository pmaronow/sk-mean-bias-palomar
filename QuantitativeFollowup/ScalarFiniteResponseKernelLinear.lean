module
public import QuantitativeFollowup.ScalarFiniteResponseLinear

@[expose] public section

/-! The finite linear form is exactly the paper's response operator,
including strict future indicators and arbitrary prescribed root mass. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper FRSB
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem parisiFreeMeasure_zero (μ : Paper.ParisiMeasure) :
    parisiFreeMeasure μ 0=(μ:Measure Paper.Overlap) := by
  have hμ : μ∈scalarFloor 0 := by simp
  simpa only [ENNReal.ofReal_zero,zero_smul,zero_add] using
    root_add_parisiFreeMeasure μ 0 (by constructor <;> norm_num) hμ

theorem scalarResponseOperator_rootMass_independent (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (φ : C(Paper.Overlap,ℝ)) (h0 : φ 0=0) (p : Paper.Overlap) :
    scalarResponseOperator β hβ μ a φ p=scalarResponseOperator β hβ μ 0 φ p := by
  rw [scalarResponseOperator_eq_full_regrouped β hβ μ a ha hμ φ h0 p,
    scalarResponseOperator_eq_full_regrouped β hβ μ 0 (by constructor <;> norm_num)
      (by simp) φ h0 p]

theorem scalarResponseOperator_eq_finite_linear (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : Paper.parisiSchemeMeasure s∈scalarFloor a)
    (φ : C(Paper.Overlap,ℝ)) (h0 : φ 0=0) (p : Paper.Overlap) :
    scalarResponseOperator β hβ (Paper.parisiSchemeMeasure s) a φ p=
      β^2*scalarFiniteResponseLinear s φ p
        (fun j r ell=>scalarResponseCoefficient j β (Paper.parisiSchemeMeasure s) p r ell) := by
  rw [scalarResponseOperator_rootMass_independent β hβ _ a ha hμ φ h0 p,
    scalarResponseOperator_eq_kernels,parisiFreeMeasure_zero,scalarFiniteResponseLinear_eq_natural]
  simp_rw [setIntegral_scalarScheme_nodes,integral_scalarScheme_nodes]
  simp only [scalarResponseCoefficient,Fin.isValue,Fin.coe_ofNat_eq_mod,Nat.reduceMod,
    scalarResponseKernel0,scalarResponseKernel1,scalarResponseKernel5,mul_assoc]

end QuantitativeFollowup
