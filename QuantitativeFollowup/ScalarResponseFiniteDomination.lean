module
public import QuantitativeFollowup.ScalarTransportSupportingCurve
public import QuantitativeFollowup.ScalarLocalSecondOrder
public import QuantitativeFollowup.ScalarResponseContinuity

@[expose] public section

/-! The finite-profile multiplier inequality follows from actual Parisi
convexity and actual transport derivatives. No response-order assumption
is supplied. The free measure is the genuine root-atom subtraction. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem scalar_response_multiplier_domination_finite_full (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : parisiSchemeMeasure s∈scalarFloor a) :
    (∫q : Paper.Overlap,φ q*scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ q
      ∂(parisiSchemeMeasure s:Measure Paper.Overlap))≤
      ∫q : Paper.Overlap,GammaPrime β (parisiSchemeMeasure s) q*φ q^2
        ∂(parisiSchemeMeasure s:Measure Paper.Overlap) := by
  have hs := second_derivative_comparison_of_local_order
    (scalarTransportFunctional β (parisiSchemeMeasure s) φ)
    (scalarTransportSupportingCurve β (parisiSchemeMeasure s) φ)
    (scalarTransportFirstDerivative β (parisiSchemeMeasure s) φ)
    (scalarTransportSupportDerivative β (parisiSchemeMeasure s) φ)
    δ _ _ hδ
    (fun u hu=>hasDerivAt_scalarTransportFunctional s β hβ φ L hφ h0 h1 δ u
      hδ hsmall (abs_lt.mpr hu))
    (fun u hu=>hasDerivAt_scalarTransportSupportingCurve s β hβ.ne' φ L hφ h0 h1 u
      ((mul_le_mul_of_nonneg_right (abs_lt.mpr hu).le L.coe_nonneg).trans_lt hsmall))
    (hasDerivAt_scalarTransportFirstDerivative_zero s β hβ φ L hφ h0 h1 δ hδ hsmall a ha hμ)
    (hasDerivAt_scalarTransportSupportDerivative_zero s β hβ.ne' φ L hφ h0 h1)
    (fun u _=>by
      rw [scalarTransportSupportingCurve_zero]
      simpa only [sub_zero] using scalarTransportSupportingCurve_convex_support β hβ.ne'
        (parisiSchemeMeasure s) φ u)
  have hpos : 0<β^2/2 := by positivity
  have hbase := le_of_mul_le_mul_left hs hpos
  have hsquare : Integrable (fun q : Paper.Overlap=>φ q^2)
      (parisiSchemeMeasure s:Measure Paper.Overlap) :=
    integrable_overlap_continuous (φ.continuous.pow 2) _
  have hmul : Integrable (fun q : Paper.Overlap=>GammaPrime β (parisiSchemeMeasure s) q*φ q^2)
      (parisiSchemeMeasure s:Measure Paper.Overlap) := by
    apply integrable_overlap_continuous
    exact ((continuousOn_GammaPrime β hβ.ne' _).comp_continuous continuous_subtype_val
      (fun q=>q.property)).mul (φ.continuous.pow 2)
  have hresponse : Integrable (fun q : Paper.Overlap=>
      φ q*scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ q)
      (parisiSchemeMeasure s:Measure Paper.Overlap) :=
    integrable_overlap_continuous (φ.continuous.mul
      (continuous_scalarResponseOperator β hβ.ne' _ a ha hμ φ)) _
  have hleft : (∫q : Paper.Overlap,φ q^2*(1-GammaPrime β (parisiSchemeMeasure s) q)
      ∂(parisiSchemeMeasure s:Measure Paper.Overlap))=
      (∫q : Paper.Overlap,φ q^2 ∂(parisiSchemeMeasure s:Measure Paper.Overlap))-
        ∫q : Paper.Overlap,GammaPrime β (parisiSchemeMeasure s) q*φ q^2
          ∂(parisiSchemeMeasure s:Measure Paper.Overlap) := by
    rw [←integral_sub hsquare hmul]
    apply integral_congr_ae
    exact .of_forall fun q=>by ring
  have hright : (∫q : Paper.Overlap,φ q*(φ q-
      scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ q)
      ∂(parisiSchemeMeasure s:Measure Paper.Overlap))=
      (∫q : Paper.Overlap,φ q^2 ∂(parisiSchemeMeasure s:Measure Paper.Overlap))-
        ∫q : Paper.Overlap,φ q*scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ q
          ∂(parisiSchemeMeasure s:Measure Paper.Overlap) := by
    rw [←integral_sub hsquare hresponse]
    apply integral_congr_ae
    exact .of_forall fun q=>by ring
  rw [hleft,hright] at hbase
  linarith

theorem scalar_response_multiplier_domination_finite (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : parisiSchemeMeasure s∈scalarFloor a) :
    (∫q : Paper.Overlap,φ q*scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ q
      ∂parisiFreeMeasure (parisiSchemeMeasure s) a)≤
      ∫q : Paper.Overlap,GammaPrime β (parisiSchemeMeasure s) q*φ q^2
        ∂parisiFreeMeasure (parisiSchemeMeasure s) a := by
  have hresponse : Continuous (fun q : Paper.Overlap=>
      φ q*scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ q) :=
    φ.continuous.mul (continuous_scalarResponseOperator β hβ.ne' _ a ha hμ φ)
  have hmul : Continuous (fun q : Paper.Overlap=>GammaPrime β (parisiSchemeMeasure s) q*φ q^2) :=
    ((continuousOn_GammaPrime β hβ.ne' _).comp_continuous continuous_subtype_val
      (fun q=>q.property)).mul (φ.continuous.pow 2)
  rw [integral_parisiFreeMeasure_continuous _ a ha hμ _ hresponse,
    integral_parisiFreeMeasure_continuous _ a ha hμ _ hmul]
  simp only [show zeroOverlap=(0:Paper.Overlap) from rfl,h0,zero_mul,
    zero_pow (by decide : 2≠0),mul_zero,sub_zero]
  exact scalar_response_multiplier_domination_finite_full s β hβ φ L hφ h0 h1
    δ hδ hsmall a ha hμ

end QuantitativeFollowup
