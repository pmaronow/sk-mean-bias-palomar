module
public import QuantitativeFollowup.FollowupCavityRestTraceColumns

@[expose] public section

/-! Actual covariance columns identify the kernel-diagonal trace with the
Hilbert-space trace. The centered paths are genuine native rest diffusions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem cavityRestCovarianceColumn_eq_covariance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p q : Paper.Overlap) :
    cavityRestCovarianceColumn D μ a p q=
      covariance (cavityRestSelfOverlap D μ p) (cavityRestSelfOverlap D μ q)
        (anisotropicMeasureSampleLaw D μ a) := by
  rw [cavityRestCovarianceColumn_apply,covariance]
  apply integral_congr_ae
  exact .of_forall fun ω=>by
    change (cavityRestSelfOverlap D μ p ω-cavityRestOverlapMean D μ a p)*
      (cavityRestSelfOverlap D μ q ω-cavityRestOverlapMean D μ a q)=_
    rw [cavityRestOverlapMean_apply,cavityRestOverlapMean_apply]

 theorem cavityRestEndpointProcess_response_pairing (D : AnisotropicSpinModel n)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0)
    (ω : AnisotropicDisorderBrownianSample n) :
    inner ℝ (cavityRestEndpointProcess D μ a ω)
      (scalarResponseL2Operator β hβ μ a ha hμ (cavityRestEndpointProcess D μ a ω))=
      ∫p : Paper.Overlap,cavityRestCenteredOverlapPath D μ a ω p*
        scalarResponseOperator β hβ μ a (cavityRestCenteredOverlapPath D μ a ω) p
        ∂parisiFreeMeasure μ a := by
  let φ:=cavityRestCenteredOverlapPath D μ a ω
  have hm : ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ φ∈
      endpointFixedL2 (parisiFreeMeasure μ a):=
    overlapCenteredL2Process_mem_endpoint _ _ _ (measurable_cavityRestOverlapPath D μ)
      1 (by norm_num) (cavityRestOverlapPath_norm_le D μ)
      (cavityRestSelfOverlap_zero D μ) hone ω
  have he : cavityRestEndpointProcess D μ a ω=
      (⟨ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ φ,hm⟩ :
        endpointFixedL2 (parisiFreeMeasure μ a)):=by
    apply Subtype.ext
    exact cavityRestEndpointProcess_coe D μ a hone ω
  rw [he]
  exact scalarResponseL2Operator_continuous_pairing β hβ μ a ha hμ φ hm

 theorem integrable_cavityRest_response_product (D : AnisotropicSpinModel n)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    Integrable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      cavityRestCenteredOverlapPath D μ a z.2 z.1*
        scalarResponseOperator β hβ μ a (cavityRestCenteredOverlapPath D μ a z.2) z.1)
      ((parisiFreeMeasure μ a).prod (anisotropicMeasureSampleLaw D μ a)) := by
  let X:=cavityRestCenteredOverlapPath D μ a
  let J:=cavityScalarContinuousResponse β hβ μ a ha hμ
  have hm : Measurable X:=measurable_cavityRestCenteredOverlapPath D μ a
  have he : Continuous (fun z : C(Paper.Overlap,ℝ)×Paper.Overlap=>z.1 z.2):=continuous_eval
  have hx : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>X z.2 z.1):=
    he.measurable.comp ((hm.comp measurable_snd).prodMk measurable_fst)
  have hj : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>J (X z.2) z.1):=
    he.measurable.comp ((J.continuous.measurable.comp (hm.comp measurable_snd)).prodMk measurable_fst)
  have hmeas : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      X z.2 z.1*J (X z.2) z.1):=hx.mul hj
  apply (integrable_const ‖J‖).mono' hmeas.aestronglyMeasurable
  exact .of_forall fun z=>by
    change ‖X z.2 z.1*J (X z.2) z.1‖ ≤ ‖J‖
    rw [norm_mul]
    have hX : ‖X z.2‖ ≤ 1:=cavityRestCenteredOverlapPath_norm_le D μ a z.2
    have hx0 : ‖X z.2 z.1‖ ≤ 1:=((X z.2).norm_coe_le_norm z.1).trans hX
    have hj0 : ‖J (X z.2) z.1‖ ≤ ‖J‖:=
      ((J (X z.2)).norm_coe_le_norm z.1).trans
        ((J.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg J) hX))
    exact (mul_le_mul hx0 hj0 (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

 theorem cavityRestResponseTrace_eq_kernel_diagonal (D : AnisotropicSpinModel n)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0) :
    cavityRestResponseTrace D β hβ μ a ha hμ=
      ∫p : Paper.Overlap,scalarResponseOperator β hβ μ a
        (cavityRestCovarianceColumn D μ a p) p ∂parisiFreeMeasure μ a := by
  have hi:=integrable_cavityRest_response_product D β hβ μ a ha hμ
  calc
    cavityRestResponseTrace D β hβ μ a ha hμ=
      ∫ω,∫p : Paper.Overlap,cavityRestCenteredOverlapPath D μ a ω p*
        scalarResponseOperator β hβ μ a (cavityRestCenteredOverlapPath D μ a ω) p
        ∂parisiFreeMeasure μ a ∂anisotropicMeasureSampleLaw D μ a:=by
      apply integral_congr_ae
      exact .of_forall (cavityRestEndpointProcess_response_pairing D β hβ μ a ha hμ hone)
    _=∫p : Paper.Overlap,∫ω,cavityRestCenteredOverlapPath D μ a ω p*
        scalarResponseOperator β hβ μ a (cavityRestCenteredOverlapPath D μ a ω) p
        ∂anisotropicMeasureSampleLaw D μ a ∂parisiFreeMeasure μ a:=
      (integral_integral_swap hi).symm
    _=∫p : Paper.Overlap,scalarResponseOperator β hβ μ a
        (cavityRestCovarianceColumn D μ a p) p ∂parisiFreeMeasure μ a:=by
      apply integral_congr_ae
      exact .of_forall fun p=>(cavityScalarResponse_covariance_column D β hβ μ a ha hμ p).symm

 theorem integrable_cavityRestResponseTrace_kernel_diagonal (D : AnisotropicSpinModel n)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    Integrable (fun p : Paper.Overlap=>scalarResponseOperator β hβ μ a
      (cavityRestCovarianceColumn D μ a p) p) (parisiFreeMeasure μ a) := by
  have hi:=integrable_cavityRest_response_product D β hβ μ a ha hμ
  exact hi.integral_prod_left.congr (.of_forall fun p=>
    (cavityScalarResponse_covariance_column D β hβ μ a ha hμ p).symm)

 theorem cavityRestResponseTrace_kernel_diagonal_hasSum (D : AnisotropicSpinModel n)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℝ (endpointFixedL2 (parisiFreeMeasure μ a))) :
    HasSum (fun i=>inner ℝ
      (scalarResponseL2Operator β hβ μ a ha hμ (cavityRestCovariance D μ a (b i))) (b i))
      (∫p : Paper.Overlap,scalarResponseOperator β hβ μ a
        (cavityRestCovarianceColumn D μ a p) p ∂parisiFreeMeasure μ a) := by
  rw [←cavityRestResponseTrace_eq_kernel_diagonal D β hβ μ a ha hμ hone]
  exact cavityRestResponseTrace_hasSum D β hβ μ a ha hμ b

end QuantitativeFollowup
