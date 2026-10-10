module
public import HexagonPaper.TreeLikelihoodEndpointRecords
public import HexagonPaper.TreeLikelihoodFullLaw
public import QuantitativeFollowup.AnisotropicRecordedNativeMarginal
public import FourPapersCommon.KernelSamplingMap

@[expose] public section

/-! True observed endpoint marginals of complete native path trees. Every
remaining subtree is integrated with its actual Markov kernel. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup FiniteTerminalGenealogy
open scoped Topology NNReal ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
variable {n:ℕ}

theorem treeNativeFullLaw_endpoint_records (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure)
    (a:ℝ) (q:ℕ→Paper.Overlap) (hq:∀k,q (k+1)≤q k)
    {j:ℕ} (T:FiniteTerminalGenealogy j):
    (treeNativeFullLaw D μ a q T).map
      (Prod.map id (treePathEndpoints (fun k=>edgePathEndpoint D (q k)) T))=
        anisotropicRecordedProfileTreeLaw D μ a q T:=by
  unfold treeNativeFullLaw anisotropicRecordedProfileTreeLaw
  have he (x:AnisotropicObservationState n):
      (treeNativePathKernel D μ q T x).map
        (treePathEndpoints (fun k=>edgePathEndpoint D (q k)) T)=
          anisotropicRecordedProfileTreeKernel D μ q T x:=by
    have hh:=congrArg (fun K:Kernel (AnisotropicObservationState n)
      (Records (AnisotropicObservationState n) (Configuration n) T)=>K x)
        (treeNativePathKernel_endpoint_records D μ q hq T)
    rw [Kernel.map_apply _ (measurable_treePathEndpoints _ (fun k=>measurable_edgePathEndpoint D (q k)) T)] at hh
    exact hh
  rw [map_compProd_map_pair _ _ _ id _ measurable_id
    (measurable_treePathEndpoints _ (fun k=>measurable_edgePathEndpoint D (q k)) T) he,Measure.map_id]

theorem treeNativePathKernel_first_endpoint (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure)
    (q:ℕ→Paper.Overlap) {j:ℕ} (T:FiniteTerminalGenealogy j) (hqq:q (j+1)≤q j):
    (treeNativePathKernel D μ q (.advance T)).map
      (fun Z=>edgePathEndpoint D (q j) Z.1)=anisotropicObservationTransition D μ (q (j+1)) (q j):=by
  haveI:IsMarkovKernel (treePathRecordKernel (treeNativeSpinKernel D)
      (fun k=>edgePhysicalPathKernel D μ (q (k+1)) (q k))
      (fun k=>edgePathEndpoint D (q k)) (fun k=>measurable_edgePathEndpoint D (q k)) T):=
    isMarkovKernel_treePathRecordKernel _ _ _ _ inferInstance (fun _=>inferInstance) T
  change (_ ⊗ₖ _).map (edgePathEndpoint D (q j) ∘ Prod.fst)=_
  rw [Kernel.map_comp_right _ measurable_fst (measurable_edgePathEndpoint D (q j)),
    ←Kernel.fst_eq,Kernel.fst_compProd,edgePhysicalPathKernel_endpoint_native D μ _ _ hqq]

theorem treeNativeFullLaw_first_endpoint (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure)
    (a:ℝ) (q:ℕ→Paper.Overlap) {j:ℕ} (T:FiniteTerminalGenealogy j) (hqq:q (j+1)≤q j):
    (treeNativeFullLaw D μ a q (.advance T)).map
      (fun z=>edgePathEndpoint D (q j) z.2.1)=
        (anisotropicObservationTransition D μ (q (j+1)) (q j)) ∘ₘ
          anisotropicObservationInitialLaw D μ a:=by
  haveI : IsMarkovKernel (treeNativePathKernel D μ q (.advance T)) :=
    treeNativePathKernel_markov D μ q (.advance T)
  let f : Records (NativeTreePath n) (Configuration n) (.advance T) → AnisotropicObservationState n :=
    fun Z => edgePathEndpoint D (q j) Z.1
  have hf : Measurable f := (measurable_edgePathEndpoint D (q j)).comp measurable_fst
  change (anisotropicObservationInitialLaw D μ a ⊗ₘ treeNativePathKernel D μ q (.advance T)).map
    (f ∘ Prod.snd) = _
  rw [←Measure.map_map hf measurable_snd]
  change ((anisotropicObservationInitialLaw D μ a ⊗ₘ treeNativePathKernel D μ q (.advance T)).snd).map f = _
  rw [Measure.snd_compProd, Measure.map_comp _ _ hf]
  have he := treeNativePathKernel_first_endpoint D μ q T hqq
  change (treeNativePathKernel D μ q (.advance T)).map f = _ at he
  rw [he]

theorem treeNativeFullLaw_first_endpoint_eq_original (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap) {j:ℕ} (T:FiniteTerminalGenealogy j)
    (hroot:q (j+1)=0):
    (treeNativeFullLaw D μ a q (.advance T)).map
      (fun z=>edgePathEndpoint D (q j) z.2.1)=
        (anisotropicMeasureSampleLaw D μ a).map (anisotropicNativeObservation D μ (q j)):=by
  have hqq:q (j+1)≤q j:=by rw [hroot];exact (q j).property.1
  rw [treeNativeFullLaw_first_endpoint D μ a q T hqq,hroot,←anisotropicNativeObservation_law]

end HexagonPaper
