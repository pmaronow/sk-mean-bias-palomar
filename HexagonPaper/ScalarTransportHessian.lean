module
public import HexagonPaper.ScalarGeneralTransportResponse
public import QuantitativeFollowup.ScalarTransportFunctionalDerivative
public import QuantitativeFollowup.SupportingPrintedScalarStabilityChainsTransport
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

@[expose] public section

/-! Actual first and second scalar Parisi transport variations for arbitrary
profiles. Uniform limits apply to physical finite-profile derivatives, with
no assumed Hessian or operator identity. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff
namespace HexagonPaper
open Paper FRSB QuantitativePaper FourPapersCommon SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

 theorem continuous_scalarTransportFirstDerivative_cylinder (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (δ : ℝ) :
    Continuous (fun z : Paper.ParisiMeasure×ScalarTransportParameter δ =>
      scalarTransportFirstDerivative β z.1 φ z.2) := by
  let A := Paper.ParisiMeasure×ScalarTransportParameter δ
  have hm : Continuous (fun z : A×Paper.Overlap => scalarTransportMeasure z.1.1 φ z.1.2) :=
    (continuous_scalarTransportMeasure φ).comp
      ((continuous_fst.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  have ht : Continuous (fun z : A×Paper.Overlap => scalarLevelTransport φ z.1.2 z.2) :=
    (continuous_scalarLevelTransport φ).comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
  have hG : Continuous (fun z : A×Paper.Overlap =>
      Gamma β (scalarTransportMeasure z.1.1 φ z.1.2) (scalarLevelTransport φ z.1.2 z.2)) := by
    convert! (continuous_scalarGamma_parameter β hβ).comp (hm.prodMk ht) using 1
  have hF : Continuous (fun z : A×Paper.Overlap =>
      φ z.2*((scalarLevelTransport φ z.1.2 z.2:ℝ)-
        Gamma β (scalarTransportMeasure z.1.1 φ z.1.2) (scalarLevelTransport φ z.1.2 z.2))) :=
    (φ.continuous.comp continuous_snd).mul ((continuous_subtype_val.comp ht).sub hG)
  have hI := continuous_integral_probability_family _ hF
    (fun z : A => z.1) continuous_fst
  exact continuous_const.mul hI

 theorem hasDerivAt_scalarTransportFunctional_general (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (u : ℝ) (hu : u∈Ioo (-δ) δ) :
    HasDerivAt (scalarTransportFunctional β μ φ) (scalarTransportFirstDerivative β μ φ u) u := by
  let D : Paper.ParisiMeasure→C(ScalarTransportParameter δ,ℝ) := fun ν =>
    ⟨fun v=>scalarTransportFirstDerivative β ν φ v,by
      convert! (continuous_scalarTransportFirstDerivative_cylinder β hβ.ne' φ δ).comp
        (continuous_const.prodMk continuous_id) using 1⟩
  have hD : Continuous D := ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_scalarTransportFirstDerivative_cylinder β hβ.ne' φ δ)
  have hDU := ContinuousMap.tendsto_iff_tendstoUniformly.mp
    ((hD.tendsto μ).comp (tendsto_parisiGridMeasure μ))
  have hU : TendstoUniformlyOn (fun n v=>scalarTransportFirstDerivative β (parisiGridMeasure μ n) φ v)
      (fun v=>scalarTransportFirstDerivative β μ φ v) atTop (Icc (-δ) δ) :=
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hDU
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hU.mono Ioo_subset_Icc_self)
    (f:=fun n=>scalarTransportFunctional β (parisiGridMeasure μ n) φ)
  · exact .of_forall fun n v hv => by
      have hd := hasDerivAt_scalarTransportFunctional (parisiGridRSBScheme μ n)
        β hβ φ L hφ h0 h1 δ v hδ hsmall (abs_lt.mpr hv)
      simpa only [parisiSchemeMeasure_grid_eq] using hd
  · intro v hv
    have hm := ((continuous_scalarTransportMeasure φ).comp
      (continuous_id.prodMk (continuous_const (y:=v)))).tendsto μ |>.comp (tendsto_parisiGridMeasure μ)
    exact (continuous_scalarParisiFunctional β).tendsto (scalarTransportMeasure μ φ v) |>.comp hm
  · exact hu

 def scalarCylinderSecondVariation (β : ℝ) (hβ : β≠0) (s : ℝ)
    (μ : ScalarFloorMeasure s) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hsmall : δ*L<1) (u : ScalarTransportParameter δ) : ℝ :=
  β^2/2*(∫q : Paper.Overlap,φ q*(φ q-
    scalarCylinderResponse β hβ s μ φ L hφ h0 h1 δ hsmall q u)
    ∂(μ.val:Measure Paper.Overlap))

 theorem continuous_scalarCylinderSecondVariation (β : ℝ) (hβ : β≠0) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hsmall : δ*L<1) :
    Continuous (fun z : ScalarFloorMeasure s×ScalarTransportParameter δ =>
      scalarCylinderSecondVariation β hβ s z.1 φ L hφ h0 h1 δ hsmall z.2) := by
  let A := ScalarFloorMeasure s×ScalarTransportParameter δ
  have hF : Continuous (fun z : A×Paper.Overlap => φ z.2*(φ z.2-
      scalarCylinderResponse β hβ s z.1.1 φ L hφ h0 h1 δ hsmall z.2 z.1.2)) :=
    (φ.continuous.comp continuous_snd).mul ((φ.continuous.comp continuous_snd).sub
      (continuous_scalarCylinderResponse_joint_level β hβ s hs φ L hφ h0 h1 δ hsmall))
  exact continuous_const.mul (continuous_integral_probability_family _ hF
    (fun z : A => z.1.val) (continuous_subtype_val.comp continuous_fst))

 theorem hasDerivAt_scalarTransportFirstDerivative_finite_at {k : ℕ} (r : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (hμ : parisiSchemeMeasure r∈scalarFloor s)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (u : ScalarTransportParameter δ) :
    HasDerivAt (scalarTransportFirstDerivative β (parisiSchemeMeasure r) φ)
      (scalarCylinderSecondVariation β hβ.ne' s ⟨parisiSchemeMeasure r,hμ⟩
        φ L hφ h0 h1 δ hsmall u) u := by
  have hT (q : Paper.Overlap) := hasDerivAt_scalarLevelTransport_coe φ L hφ h0 h1 u
    (scalarTransportParameter_small δ L hsmall u) q
  have hG (q : Paper.Overlap) := hasDerivAt_scalarTransportGamma_finite_at r β hβ φ L hφ h0 h1
    s hs hμ u (scalarTransportParameter_small δ L hsmall u) q
  simp_rw [←scalarCylinderRelabelledDirection_eq φ L hφ h0 h1 δ hsmall u] at hG
  exact (hasDerivAt_scalarScheme_integral r _ _ u
    (fun q => ((hT q).sub (hG q)).const_mul (φ q))).const_mul (β^2/2)

 theorem hasDerivAt_scalarTransportFirstDerivative_general_at (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (u : ℝ) (hu : u∈Ioo (-δ) δ) :
    HasDerivAt (scalarTransportFirstDerivative β μ φ)
      (scalarCylinderSecondVariation β hβ.ne' s ⟨μ,hμ⟩ φ L hφ h0 h1 δ hsmall
        ⟨u,⟨hu.1.le,hu.2.le⟩⟩) u := by
  let μn : ℕ→ScalarFloorMeasure s := fun n =>
    ⟨parisiGridMeasure μ n,parisiGridMeasure_mem_scalarFloor μ s hμ n⟩
  let D : ScalarFloorMeasure s→C(ScalarTransportParameter δ,ℝ) := fun ν =>
    ⟨scalarCylinderSecondVariation β hβ.ne' s ν φ L hφ h0 h1 δ hsmall,by
      convert! (continuous_scalarCylinderSecondVariation β hβ.ne' s hs φ L hφ h0 h1 δ hsmall).comp
        (continuous_const.prodMk continuous_id) using 1⟩
  have hD : Continuous D := ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_scalarCylinderSecondVariation β hβ.ne' s hs φ L hφ h0 h1 δ hsmall)
  have hweak : Tendsto μn atTop (𝓝 (⟨μ,hμ⟩ : ScalarFloorMeasure s)) :=
    tendsto_subtype_rng.mpr (tendsto_parisiGridMeasure μ)
  have hDU := ContinuousMap.tendsto_iff_tendstoUniformly.mp ((hD.tendsto ⟨μ,hμ⟩).comp hweak)
  let d : ScalarFloorMeasure s→ℝ→ℝ := fun ν v =>
    D ν (projIcc (-δ) δ (by linarith) v)
  have hU : TendstoUniformly (fun n=>d (μn n)) (d ⟨μ,hμ⟩) atTop :=
    hDU.comp (fun v=>projIcc (-δ) δ (by linarith) v)
  have hd : HasDerivAt (scalarTransportFirstDerivative β μ φ) (d ⟨μ,hμ⟩ u) u := by
    apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hU.tendstoUniformlyOn
      (f:=fun n=>scalarTransportFirstDerivative β (parisiGridMeasure μ n) φ)
    · exact .of_forall fun n v hv => by
        have hdv := hasDerivAt_scalarTransportFirstDerivative_finite_at (parisiGridRSBScheme μ n)
          β hβ s hs (by rw [parisiSchemeMeasure_grid_eq];exact parisiGridMeasure_mem_scalarFloor μ s hμ n)
          φ L hφ h0 h1 δ hδ hsmall ⟨v,⟨hv.1.le,hv.2.le⟩⟩
        simpa only [d,D,ContinuousMap.coe_mk,μn,projIcc_of_mem (by linarith) ⟨hv.1.le,hv.2.le⟩,
          parisiSchemeMeasure_grid_eq] using hdv
    · intro v hv
      have hc : Continuous (fun ν : Paper.ParisiMeasure => scalarTransportFirstDerivative β ν φ v) := by
        convert! (continuous_scalarTransportFirstDerivative_cylinder β hβ.ne' φ δ).comp
          (continuous_id.prodMk (continuous_const (y:=(⟨v,⟨hv.1.le,hv.2.le⟩⟩:ScalarTransportParameter δ)))) using 1
      exact (hc.tendsto μ).comp (tendsto_parisiGridMeasure μ)
    · exact hu
  simpa only [d,D,ContinuousMap.coe_mk,projIcc_of_mem (by linarith) ⟨hu.1.le,hu.2.le⟩] using hd

 theorem scalarCylinderRelabelledDirection_zero (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) :
    scalarCylinderRelabelledDirection φ L hφ h0 h1 δ hsmall
      ⟨0,⟨by linarith,hδ.le⟩⟩=φ := by
  ext q
  have hh := scalarCylinderRelabelledDirection_transport φ L hφ h0 h1 δ hsmall
    ⟨0,⟨by linarith,hδ.le⟩⟩ q
  simpa only [scalarLevelTransport_zero] using hh

 theorem hasDerivAt_deriv_scalarTransportFunctional_general_zero (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) :
    HasDerivAt (deriv (scalarTransportFunctional β μ φ))
      (β^2/2*(∫q : Paper.Overlap,φ q*(φ q-scalarResponseOperator β hβ.ne' μ s φ q)
        ∂parisiFreeMeasure μ s)) 0 := by
  have hz : (0:ℝ)∈Ioo (-δ) δ := ⟨by linarith,hδ⟩
  have hd := hasDerivAt_scalarTransportFirstDerivative_general_at β hβ μ s hs hμ
    φ L hφ h0 h1 δ hδ hsmall 0 hz
  simp only [scalarCylinderSecondVariation,scalarCylinderResponse,
    scalarTransportMeasure_zero,scalarLevelTransport_zero,
    scalarCylinderRelabelledDirection_zero φ L hφ h0 h1 δ hδ hsmall] at hd
  have he : deriv (scalarTransportFunctional β μ φ)=ᶠ[𝓝 (0:ℝ)]
      scalarTransportFirstDerivative β μ φ := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with u hu
    exact (hasDerivAt_scalarTransportFunctional_general β hβ μ φ L hφ h0 h1 δ hδ hsmall u hu).deriv
  have hfree : (∫q : Paper.Overlap,φ q*(φ q-scalarResponseOperator β hβ.ne' μ s φ q)
      ∂parisiFreeMeasure μ s)=
      ∫q : Paper.Overlap,φ q*(φ q-scalarResponseOperator β hβ.ne' μ s φ q)
        ∂(μ:Measure Paper.Overlap) := by
    have hc : Continuous (fun q : Paper.Overlap=>φ q*(φ q-scalarResponseOperator β hβ.ne' μ s φ q)) :=
      φ.continuous.mul (φ.continuous.sub (continuous_scalarResponseOperator β hβ.ne' μ s hs hμ φ))
    rw [integral_parisiFreeMeasure_continuous μ s hs hμ
      (fun q : Paper.Overlap=>φ q*(φ q-scalarResponseOperator β hβ.ne' μ s φ q)) hc]
    simp only [show zeroOverlap=(0:Paper.Overlap) from rfl,h0,zero_mul,mul_zero,sub_zero]
  rw [hfree]
  exact hd.congr_of_eventuallyEq he

 theorem scalar_transport_first_variation (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (u : ℝ) (hu : u∈Ioo (-δ) δ) :
    HasDerivAt (scalarTransportFunctional β μ φ)
      (β^2/2*(∫q : Paper.Overlap,φ q*((scalarLevelTransport φ u q:ℝ)-
        Gamma β (scalarTransportMeasure μ φ u) (scalarLevelTransport φ u q))
        ∂parisiFreeMeasure μ s)) u := by
  have hd := hasDerivAt_scalarTransportFunctional_general β hβ μ φ L hφ h0 h1 δ hδ hsmall u hu
  apply hd.congr_deriv
  unfold scalarTransportFirstDerivative
  congr 1
  have hc : Continuous (fun q : Paper.Overlap=>φ q*((scalarLevelTransport φ u q:ℝ)-
      Gamma β (scalarTransportMeasure μ φ u) (scalarLevelTransport φ u q))) :=
    φ.continuous.mul
      ((continuous_subtype_val.comp (continuous_scalarLevelTransport_parameter φ u)).sub
        ((continuousOn_Gamma β hβ.ne' _).comp_continuous
          (continuous_subtype_val.comp (continuous_scalarLevelTransport_parameter φ u))
          (fun q=>(scalarLevelTransport φ u q).property)))
  rw [integral_parisiFreeMeasure_continuous μ s hs hμ
    (fun q : Paper.Overlap=>φ q*((scalarLevelTransport φ u q:ℝ)-
      Gamma β (scalarTransportMeasure μ φ u) (scalarLevelTransport φ u q))) hc]
  simp only [show zeroOverlap=(0:Paper.Overlap) from rfl,h0,zero_mul,mul_zero,sub_zero]

 theorem scalar_transport_second_variation_inner (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (φ : endpointFixedLipschitzTests) (L : ℝ≥0) (hφ : LipschitzWith L φ.val)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) :
    let f := endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ s) φ
    HasDerivAt (deriv (scalarTransportFunctional β μ φ.val))
      (β^2/2*inner ℝ f (f-scalarResponseL2Operator β hβ.ne' μ s hs hμ f)) 0 := by
  dsimp only
  rw [supporting_printed_scalar_response_I_sub_J_pairing]
  exact hasDerivAt_deriv_scalarTransportFunctional_general_zero β hβ μ s hs hμ
    φ.val L hφ φ.property.1 φ.property.2.1 δ hδ hsmall

end HexagonPaper
