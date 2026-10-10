module
public import QuantitativeFollowup.ScalarTransportPointwiseResponse
public import QuantitativeFollowup.ScalarScoreConditioning

@[expose] public section

/-! Retained Gaussian-coordinate observables are the literal fields of the
constructed diffusion. The local terminal-spin score has expectation zero
by the actual whole-past conditional spin law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper FRSB
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem scalarSelectedHistory_node (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (ω : Paper.BrownianSample) (i : Fin (k+3)) :
    scalarSelectedHistory s β hβ ω i=
      parisiPhysicalSplitState β 0 (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s i) ω := by
  rw [parisiPhysicalSplitState_eq_selected β hβ]
  unfold scalarSelectedHistory FRSB.historySample
  congr 1
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (scalarSchemeTransportNode s i).property.1,
    scalarSchemeTransportNode_eq_clock s i (by omega)]

theorem scalarFiniteNodeGradient_physical (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (ω : Paper.BrownianSample) (i : Fin (k+3)) :
    scalarFiniteNodeGradient s β (WithLp.toLp 2 (scalarSelectedHistory s β hβ ω)) i=
      M β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s i) ω := by
  unfold scalarFiniteNodeGradient
  simp only [WithLp.ofLp_toLp]
  rw [scalarSelectedHistory_node,←scalarSchemeTransportNode_eq_clock s i (by omega)]
  exact scalarGradient_physicalSplitState β hβ _ _ _

theorem scalarFiniteNodeHessian_physical (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (ω : Paper.BrownianSample) (i : Fin (k+3)) :
    scalarFiniteNodeHessian s β (WithLp.toLp 2 (scalarSelectedHistory s β hβ ω)) i=
      C β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s i) ω := by
  unfold scalarFiniteNodeHessian
  simp only [WithLp.ofLp_toLp]
  rw [scalarSelectedHistory_node,←scalarSchemeTransportNode_eq_clock s i (by omega)]
  exact scalarHessian_physicalSplitState β hβ _ _ _

theorem integral_scalar_centered_terminal_score (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    (∫z,M β μ p z.1*C β μ p z.1*(Paper.spinSign z.2-M β μ p z.1)
      ∂scalarMarkedSpinLaw β hβ μ)=0 := by
  let P:=scalarMarkedSpinLaw β hβ μ
  let F:=fun z : Paper.BrownianSample×Bool=>M β μ p z.1*C β μ p z.1*Paper.spinSign z.2
  let H:=fun z : Paper.BrownianSample×Bool=>M β μ p z.1^2*C β μ p z.1
  have hM : Measurable (fun z : Paper.BrownianSample×Bool=>M β μ p z.1) :=
    (measurable_M β μ p p.property).comp measurable_fst
  have hC : Measurable (fun z : Paper.BrownianSample×Bool=>C β μ p z.1) :=
    (measurable_C β hβ μ p.property).comp measurable_fst
  have hF : Measurable F := (hM.mul hC).mul ((measurable_of_finite Paper.spinSign).comp measurable_snd)
  have hH : Measurable H := (hM.pow_const 2).mul hC
  have hiF : Integrable F P := (integrable_const (1:ℝ)).mono' hF.aestronglyMeasurable
    (.of_forall fun z=>by
      dsimp only [F]
      rw [norm_mul,norm_mul,show ‖Paper.spinSign z.2‖=1 by cases z.2 <;> norm_num [Paper.spinSign]]
      simpa only [one_mul,mul_one] using mul_le_mul (scalar_M_norm_le_one β μ p z.1)
        (norm_C_le_one β μ p z.1) (norm_nonneg _) zero_le_one)
  have hiH : Integrable H P := (integrable_const (1:ℝ)).mono' hH.aestronglyMeasurable
    (.of_forall fun z=>by
      dsimp only [H]
      rw [norm_mul,norm_pow]
      exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) (scalar_M_norm_le_one β μ p z.1))
        (norm_C_le_one β μ p z.1) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have he : (fun z : Paper.BrownianSample×Bool=>M β μ p z.1*C β μ p z.1*
      (Paper.spinSign z.2-M β μ p z.1))=(fun z=>F z-H z) := by funext z;dsimp only [F,H];ring
  rw [he,integral_sub hiF hiH]
  have hfirst:=integral_scalarMarkedSpinLaw_mean_curvature_sign β hβ μ p
  have hsecond:=integral_scalarMarkedSpinLaw_sample β hβ μ
    (fun ω=>M β μ p ω^2*C β μ p ω)
    (((measurable_M β μ p p.property).pow_const 2).mul (measurable_C β hβ μ p.property))
  change (∫z,F z ∂P)-(∫z,H z ∂P)=0
  dsimp only [F,H,P]
  rw [hfirst,hsecond,sub_self]

theorem integral_scalarFinite_centered_terminal_score (s : RSBScheme k) (β : ℝ)
    (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) :
    (∫z,2*β^2*φ (scalarSchemeTransportNode s p)*
      scalarFiniteNodeGradient s β (WithLp.toLp 2 (scalarSelectedHistory s β hβ z.1)) p*
      scalarFiniteNodeHessian s β (WithLp.toLp 2 (scalarSelectedHistory s β hβ z.1)) p*
      (Paper.spinSign z.2-scalarFiniteNodeGradient s β
        (WithLp.toLp 2 (scalarSelectedHistory s β hβ z.1)) p)
      ∂scalarMarkedSpinLaw β hβ (Paper.parisiSchemeMeasure s))=0 := by
  simp_rw [scalarFiniteNodeGradient_physical s β hβ,scalarFiniteNodeHessian_physical s β hβ]
  have he (z : Paper.BrownianSample×Bool) :
      2*β^2*φ (scalarSchemeTransportNode s p)*M β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p) z.1*
        C β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p) z.1*
        (Paper.spinSign z.2-M β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p) z.1)=
      (2*β^2*φ (scalarSchemeTransportNode s p))*(
        M β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p) z.1*
        C β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p) z.1*
        (Paper.spinSign z.2-M β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p) z.1)) := by ring
  simp_rw [he]
  rw [integral_const_mul,integral_scalar_centered_terminal_score,mul_zero]

end QuantitativeFollowup
