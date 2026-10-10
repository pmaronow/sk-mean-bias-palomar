module
public import QuantitativeFollowup.FollowupCavityRestTraceExtension

@[expose] public section

/-! The literal scalar response is a bounded operator on continuous paths.
Its action commutes with the genuine rest covariance-column integral. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem cavityScalarContinuousResponse_norm_le (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (φ : C(Paper.Overlap,ℝ)) :
    ‖scalarResponseContinuousLinearMap β hβ μ a ha hμ φ‖ ≤ scalarResponseL2Bound β*‖φ‖ := by
  apply ((scalarResponseContinuousLinearMap β hβ μ a ha hμ φ).norm_le
    (mul_nonneg (scalarResponseL2Bound_nonneg β) (norm_nonneg φ))).mpr
  intro p
  have hp:=scalar_response_norm_pointwise β hβ μ a ha φ p
  have hpoint : |φ p|≤‖φ‖:=φ.norm_coe_le_norm p
  have hi : (∫q,|φ q| ∂parisiFreeMeasure μ a)≤‖φ‖ := by
    have hh:=norm_integral_le_of_norm_le_const (μ:=parisiFreeMeasure μ a)
      (f:=fun q=>|φ q|) (.of_forall fun q=>by
        simpa only [Real.norm_eq_abs,abs_abs] using φ.norm_coe_le_norm q)
    have hm:=scalarFreeMeasure_mass_le_one μ a ha
    have h0 : 0≤∫q,|φ q| ∂parisiFreeMeasure μ a:=integral_nonneg fun q=>abs_nonneg _
    rw [Real.norm_eq_abs,abs_of_nonneg h0] at hh
    exact hh.trans (mul_le_of_le_one_right (norm_nonneg φ) hm)
  have hc : 0≤6*β^2*scalarResponseKernelBound β:=by
    have hb:=scalarResponseKernelBound_ge_one β
    positivity
  change ‖scalarResponseOperator β hβ μ a φ p‖≤_
  calc
    _≤6*β^2*scalarResponseKernelBound β*(|φ p|+∫q,|φ q| ∂parisiFreeMeasure μ a):=hp
    _≤6*β^2*scalarResponseKernelBound β*(‖φ‖+‖φ‖):=
      mul_le_mul_of_nonneg_left (add_le_add hpoint hi) hc
    _=scalarResponseL2Bound β*‖φ‖:=by unfold scalarResponseL2Bound;ring

 def cavityScalarContinuousResponse (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    C(Paper.Overlap,ℝ)→L[ℝ]C(Paper.Overlap,ℝ):=
  (scalarResponseContinuousLinearMap β hβ μ a ha hμ).mkContinuous
    (scalarResponseL2Bound β) (cavityScalarContinuousResponse_norm_le β hβ μ a ha hμ)

 theorem measurable_cavityRestCenteredOverlapPath (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Measurable (cavityRestCenteredOverlapPath D μ a):=
  (measurable_cavityRestOverlapPath D μ).sub measurable_const

 def cavityRestCovarianceColumn (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (p : Paper.Overlap) : C(Paper.Overlap,ℝ):=
  ∫ω,(cavityRestCenteredOverlapPath D μ a ω p) • cavityRestCenteredOverlapPath D μ a ω
    ∂anisotropicMeasureSampleLaw D μ a

 theorem integrable_cavityRestCovarianceColumn_input (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    Integrable (fun ω=>(cavityRestCenteredOverlapPath D μ a ω p) •
      cavityRestCenteredOverlapPath D μ a ω) (anisotropicMeasureSampleLaw D μ a) := by
  have hm:=measurable_cavityRestCenteredOverlapPath D μ a
  have he:=((ContinuousMap.evalCLM ℝ p).continuous.measurable.comp hm).smul hm
  apply (integrable_const (1:ℝ)).mono' he.aestronglyMeasurable
  exact .of_forall fun ω=>by
    change ‖(cavityRestCenteredOverlapPath D μ a ω p) • cavityRestCenteredOverlapPath D μ a ω‖ ≤ 1
    rw [norm_smul]
    exact (mul_le_mul
      (((cavityRestCenteredOverlapPath D μ a ω).norm_coe_le_norm p).trans
        (cavityRestCenteredOverlapPath_norm_le D μ a ω))
      (cavityRestCenteredOverlapPath_norm_le D μ a ω) (norm_nonneg _) (by norm_num)).trans_eq
        (by norm_num)

 theorem cavityRestCovarianceColumn_apply (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p q : Paper.Overlap) :
    cavityRestCovarianceColumn D μ a p q=
      ∫ω,cavityRestCenteredOverlapPath D μ a ω p*cavityRestCenteredOverlapPath D μ a ω q
        ∂anisotropicMeasureSampleLaw D μ a := by
  rw [cavityRestCovarianceColumn,ContinuousMap.integral_apply
    (integrable_cavityRestCovarianceColumn_input D μ a p)]
  rfl

 theorem cavityScalarResponse_covariance_column (D : AnisotropicSpinModel n)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (p : Paper.Overlap) :
    scalarResponseOperator β hβ μ a (cavityRestCovarianceColumn D μ a p) p=
      ∫ω,cavityRestCenteredOverlapPath D μ a ω p*
        scalarResponseOperator β hβ μ a (cavityRestCenteredOverlapPath D μ a ω) p
        ∂anisotropicMeasureSampleLaw D μ a := by
  let J:=cavityScalarContinuousResponse β hβ μ a ha hμ
  have hi:=integrable_cavityRestCovarianceColumn_input D μ a p
  change J (cavityRestCovarianceColumn D μ a p) p=_
  rw [cavityRestCovarianceColumn,←J.integral_comp_comm hi,
    ContinuousMap.integral_apply (J.integrable_comp hi)]
  apply integral_congr_ae
  exact .of_forall fun ω=>by
    change J ((cavityRestCenteredOverlapPath D μ a ω p) • cavityRestCenteredOverlapPath D μ a ω) p = _
    rw [map_smul]
    rfl

end QuantitativeFollowup
