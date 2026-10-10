module
public import QuantitativeFollowup.ScalarTransportFunctionalDerivative
public import QuantitativeFollowup.ScalarResponseL2Operator

@[expose] public section

/-! The printed transport derivatives on the actual free measure.
Endpoint-fixed tests remove exactly the prescribed root atom, even when
the profile has additional mass at zero. The second derivative is the
genuine completed L² response pairing. -/
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper FourPapersCommon SpinGlass.Targets
variable {k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem supporting_printed_scalar_transport_first (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (hu : |u|<δ)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : parisiSchemeMeasure s∈scalarFloor a) :
    HasDerivAt (scalarTransportFunctional β (parisiSchemeMeasure s) φ)
      (β^2/2*(∫q : Paper.Overlap,φ q*((scalarLevelTransport φ u q:ℝ)-
        Gamma β (scalarTransportMeasure (parisiSchemeMeasure s) φ u)
          (scalarLevelTransport φ u q)) ∂parisiFreeMeasure (parisiSchemeMeasure s) a)) u := by
  have hc : Continuous (fun q : Paper.Overlap=>φ q*((scalarLevelTransport φ u q:ℝ)-
      Gamma β (scalarTransportMeasure (parisiSchemeMeasure s) φ u) (scalarLevelTransport φ u q))) :=
    φ.continuous.mul ((continuous_subtype_val.comp (continuous_scalarLevelTransport_parameter φ u)).sub
      ((continuousOn_Gamma β hβ.ne' _).comp_continuous
        (continuous_subtype_val.comp (continuous_scalarLevelTransport_parameter φ u))
        (fun q=>(scalarLevelTransport φ u q).property)))
  rw [integral_parisiFreeMeasure_continuous _ a ha hμ _ hc]
  simp only [show zeroOverlap=(0:Paper.Overlap) from rfl,h0,zero_mul,mul_zero,sub_zero]
  exact hasDerivAt_scalarTransportFunctional s β hβ φ L hφ h0 h1 δ u hδ hsmall hu

theorem supporting_printed_scalar_transport_second_free (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : parisiSchemeMeasure s∈scalarFloor a) :
    HasDerivAt (deriv (scalarTransportFunctional β (parisiSchemeMeasure s) φ))
      (β^2/2*(∫q : Paper.Overlap,φ q*(φ q-
        scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ q)
          ∂parisiFreeMeasure (parisiSchemeMeasure s) a)) 0 := by
  have hc : Continuous (fun q : Paper.Overlap=>φ q*(φ q-
      scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ q)) :=
    φ.continuous.mul (φ.continuous.sub
      (continuous_scalarResponseOperator β hβ.ne' _ a ha hμ φ))
  rw [integral_parisiFreeMeasure_continuous _ a ha hμ _ hc]
  simp only [show zeroOverlap=(0:Paper.Overlap) from rfl,h0,zero_mul,mul_zero,sub_zero]
  exact hasDerivAt_deriv_scalarTransportFunctional_zero s β hβ φ L hφ h0 h1 δ hδ hsmall a ha hμ

theorem supporting_printed_scalar_response_I_sub_J_pairing
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (φ : endpointFixedLipschitzTests) :
    let f := endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) φ
    inner ℝ f (f-scalarResponseL2Operator β hβ μ a ha hμ f) =
      ∫q : Paper.Overlap,φ.val q*(φ.val q-scalarResponseOperator β hβ μ a φ.val q)
        ∂parisiFreeMeasure μ a := by
  dsimp only
  rw [inner_sub_right,scalarResponseL2Operator_test_pairing]
  have hself : inner ℝ (endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) φ)
      (endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) φ) =
      ∫q : Paper.Overlap,φ.val q^2∂parisiFreeMeasure μ a := by
    change inner ℝ (ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ φ.val)
      (ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ φ.val)=_
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [φ.val.coeFn_toLp (p:=2) (μ:=parisiFreeMeasure μ a) (𝕜:=ℝ)] with q hq
    rw [hq]
    simp only [RCLike.inner_apply,conj_trivial,pow_two]
  have hi (g : Paper.Overlap→ℝ) (hg : Continuous g) : Integrable g (parisiFreeMeasure μ a) := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      hg.continuousOn.integrableOn_compact (μ:=parisiFreeMeasure μ a) isCompact_univ
  have hi1 : Integrable (fun q : Paper.Overlap=>φ.val q^2) (parisiFreeMeasure μ a) :=
    hi _ (φ.val.continuous.pow 2)
  have hi2 : Integrable (fun q : Paper.Overlap=>φ.val q*scalarResponseOperator β hβ μ a φ.val q)
      (parisiFreeMeasure μ a) :=
    hi _ (φ.val.continuous.mul (continuous_scalarResponseOperator β hβ μ a ha hμ φ.val))
  rw [hself,←integral_sub hi1 hi2]
  apply integral_congr_ae
  exact .of_forall fun q=>by ring

theorem supporting_printed_scalar_transport_second_inner (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ : endpointFixedLipschitzTests) (L : ℝ≥0)
    (hφ : LipschitzWith L φ.val) (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : parisiSchemeMeasure s∈scalarFloor a) :
    let f := endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure (parisiSchemeMeasure s) a) φ
    HasDerivAt (deriv (scalarTransportFunctional β (parisiSchemeMeasure s) φ.val))
      (β^2/2*inner ℝ f (f-scalarResponseL2Operator β hβ.ne' (parisiSchemeMeasure s) a ha hμ f)) 0 := by
  dsimp only
  rw [supporting_printed_scalar_response_I_sub_J_pairing]
  exact supporting_printed_scalar_transport_second_free s β hβ φ.val L hφ
    φ.property.1 φ.property.2.1 δ hδ hsmall a ha hμ

end QuantitativeFollowup
