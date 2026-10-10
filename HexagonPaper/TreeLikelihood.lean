module
public import HexagonPaper.TreeLikelihoodFullLaw
public import HexagonPaper.TreeLikelihoodEndpointRecords

@[expose] public section

/-! Complete source tree likelihood and its common normalizer, with
actual native endpoint records and all arbitrary profile atoms retained. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ENNReal
namespace HexagonPaper
open FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

theorem treeNativeFullLaw_endpoint_records_direct (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : ∀j,q (j+1)≤q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j):
    (treeNativeFullLaw D μ a q T).map
      (Prod.map id (treePathEndpoints (fun j=>edgePathEndpoint D (q j)) T))=
      anisotropicRecordedProfileTreeLaw D μ a q T:=by
  unfold treeNativeFullLaw anisotropicRecordedProfileTreeLaw
  rw [←Measure.compProd_map (measurable_treePathEndpoints _ (fun j=>measurable_edgePathEndpoint D (q j)) T),
    treeNativePathKernel_endpoint_records D μ q hq T]

theorem treePrintedFullDensity_normalized (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (h0 : q 0=1) (hq : ∀j,q (j+1)≤q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hroot : q j=0):
    ∫⁻p,treePrintedFullDensity D μ a q T p ∂treeReferenceFullLaw D q T=1:=by
  have he:treeNativeFullLaw D μ a q T univ=1:=measure_univ
  rw [treeNativeFullLaw_printed_density D μ a hμ q h0 hq T hroot,
    MeasureTheory.withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at he
  exact he

theorem treePrintedFullDensity_common_normalizer (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (h0 : q 0=1) (hq : ∀j,q (j+1)≤q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hroot : q j=0):
    (∫⁻p,ENNReal.ofReal (Real.exp (treeNativeTerminalEnergy D q T p.1 p.2-
      ∫v,treeNativeFullPotential D μ q T p.1 p.2 v ∂treePathWeight μ a q T))
        ∂treeReferenceFullLaw D q T)=ENNReal.ofReal (anisotropicMeasureOuterPartition D μ a):=by
  have hw:(fun p:AnisotropicObservationState n×Records (NativeTreePath n) (Configuration n) T=>
      ENNReal.ofReal (Real.exp (treeNativeTerminalEnergy D q T p.1 p.2-
        ∫v,treeNativeFullPotential D μ q T p.1 p.2 v ∂treePathWeight μ a q T)))=
      fun p=>ENNReal.ofReal (anisotropicMeasureOuterPartition D μ a)*treePrintedFullDensity D μ a q T p:=by
    funext p
    unfold treePrintedFullDensity
    rw [←ENNReal.ofReal_mul (anisotropicMeasureOuterPartition_pos D μ a).le]
    congr 1
    field_simp [(anisotropicMeasureOuterPartition_pos D μ a).ne']
  rw [hw,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    treePrintedFullDensity_normalized D μ a hμ q h0 hq T hroot,mul_one]

theorem tree_likelihood_arbitrary_profile (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (h0 : q 0=1) (hq : ∀j,q (j+1)≤q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hroot : q j=0):
    treeNativeFullLaw D μ a q T=(treeReferenceFullLaw D q T).withDensity
      (treePrintedFullDensity D μ a q T) ∧
    (treePathWeight μ a q T).real univ=(FiniteCascadeGenealogy.leafCount T.asGenealogy:ℝ)-a ∧
    (∫⁻p,treePrintedFullDensity D μ a q T p ∂treeReferenceFullLaw D q T)=1 ∧
    (treeNativeFullLaw D μ a q T).map
      (Prod.map id (treePathEndpoints (fun j=>edgePathEndpoint D (q j)) T))=
      anisotropicRecordedProfileTreeLaw D μ a q T:=
  ⟨treeNativeFullLaw_printed_density D μ a hμ q h0 hq T hroot,
    treePathWeight_mass μ a hμ q h0 hq T,
    treePrintedFullDensity_normalized D μ a hμ q h0 hq T hroot,
    treeNativeFullLaw_endpoint_records_direct D μ a q hq T⟩

end HexagonPaper
