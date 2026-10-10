module
public import HexagonPaper.CavityCouplingTreeTransportGeneric
public import HexagonPaper.CavityCouplingPathTranslation
public import HexagonPaper.TreeLikelihoodNative

@[expose] public section

/-! Concrete unit-coupling transport of the genuine whole native tree,
and deterministic coupling translation of its genuine Gaussian/counting
reference. Every edge, branch and marked terminal spin is retained. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup FiniteTerminalGenealogy
open scoped Topology NNReal ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem cavityCoupling_native_spin_kernel (D : AnisotropicSpinModel n):
    treeNativeSpinKernel D=(treeNativeSpinKernel (anisotropicUnitCouplings D)).comap
      (cavityCouplingStartRescaling D) (cavityCouplingStartRescaling D).measurable := by
  ext z : 1
  simp only [treeNativeSpinKernel,anisotropicTerminalSpinKernel,Kernel.comap_apply]
  rw [cavityCouplingStartRescaling_parameter,anisotropicEnergyMap_unitCouplings]

theorem cavityCoupling_native_tree_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (hq : ∀j,q (j+1)≤q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j):
    (treeNativePathKernel D μ q T).map
      (cavityTreeRecordPathMap (cavityCouplingPathRescaling D) T)=
      (treeNativePathKernel (anisotropicUnitCouplings D) μ q T).comap
        (cavityCouplingStartRescaling D) (cavityCouplingStartRescaling D).measurable := by
  haveI : ∀j,IsFiniteKernel (edgePhysicalPathKernel D μ (q (j+1)) (q j)):=fun _=>by infer_instance
  haveI : ∀j,IsFiniteKernel
      (edgePhysicalPathKernel (anisotropicUnitCouplings D) μ (q (j+1)) (q j)):=fun _=>by infer_instance
  exact cavityTreeRecordKernel_natural (treeNativeSpinKernel D)
    (treeNativeSpinKernel (anisotropicUnitCouplings D))
    (fun j=>edgePhysicalPathKernel D μ (q (j+1)) (q j))
    (fun j=>edgePhysicalPathKernel (anisotropicUnitCouplings D) μ (q (j+1)) (q j))
    (fun j=>edgePathEndpoint D (q j))
    (fun j=>edgePathEndpoint (anisotropicUnitCouplings D) (q j))
    (fun j=>measurable_edgePathEndpoint D (q j))
    (fun j=>measurable_edgePathEndpoint (anisotropicUnitCouplings D) (q j))
    (cavityCouplingStartRescaling D) (cavityCouplingPathRescaling D)
    (cavityCouplingStartRescaling D).measurable (measurable_cavityCouplingPathRescaling D)
    (cavityCoupling_native_spin_kernel D)
    (fun j=>cavityCoupling_physical_path_kernel D μ _ _ (hq j))
    (fun j Z=>cavityCouplingPathRescaling_endpoint D (q j) Z) T

theorem cavityCoupling_reference_tree_kernel (D : AnisotropicSpinModel n)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j):
    (treeReferencePathKernel D q T).map
      (cavityTreeRecordPathMap (cavityCouplingPathRescaling D) T)=
      (treeReferencePathKernel (anisotropicUnitCouplings D) q T).comap
        (cavityCouplingStartRescaling D) (cavityCouplingStartRescaling D).measurable := by
  haveI : ∀j,IsFiniteKernel (edgeReferencePathKernel D (q (j+1)) (q j)):=fun _=>by infer_instance
  haveI : ∀j,IsFiniteKernel
      (edgeReferencePathKernel (anisotropicUnitCouplings D) (q (j+1)) (q j)):=fun _=>by infer_instance
  exact cavityTreeRecordKernel_natural (Kernel.const _ (Measure.count:Measure (Configuration n)))
    (Kernel.const _ (Measure.count:Measure (Configuration n)))
    (fun j=>edgeReferencePathKernel D (q (j+1)) (q j))
    (fun j=>edgeReferencePathKernel (anisotropicUnitCouplings D) (q (j+1)) (q j))
    (fun j=>edgePathEndpoint D (q j))
    (fun j=>edgePathEndpoint (anisotropicUnitCouplings D) (q j))
    (fun j=>measurable_edgePathEndpoint D (q j))
    (fun j=>measurable_edgePathEndpoint (anisotropicUnitCouplings D) (q j))
    (cavityCouplingStartRescaling D) (cavityCouplingPathRescaling D)
    (cavityCouplingStartRescaling D).measurable (measurable_cavityCouplingPathRescaling D)
    (by ext z:1;rw [Kernel.comap_apply,Kernel.const_apply,Kernel.const_apply])
    (fun j=>cavityCoupling_reference_path_kernel D _ _)
    (fun j Z=>cavityCouplingPathRescaling_endpoint D (q j) Z) T

theorem cavityCoupling_reference_tree_translation_kernel (D : AnisotropicSpinModel n)
    (q : ℕ→Paper.Overlap) (h : AnisotropicDisorder n)
    {j : ℕ} (T : FiniteTerminalGenealogy j):
    (treeReferencePathKernel D q T).map
      (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T)=
      (treeReferencePathKernel D q T).comap
        (cavityCouplingStartTranslation h) (measurable_cavityCouplingStartTranslation h) := by
  haveI : ∀j,IsFiniteKernel (edgeReferencePathKernel D (q (j+1)) (q j)):=fun _=>by infer_instance
  exact cavityTreeRecordKernel_natural (Kernel.const _ (Measure.count:Measure (Configuration n)))
    (Kernel.const _ (Measure.count:Measure (Configuration n)))
    (fun j=>edgeReferencePathKernel D (q (j+1)) (q j))
    (fun j=>edgeReferencePathKernel D (q (j+1)) (q j))
    (fun j=>edgePathEndpoint D (q j)) (fun j=>edgePathEndpoint D (q j))
    (fun j=>measurable_edgePathEndpoint D (q j)) (fun j=>measurable_edgePathEndpoint D (q j))
    (cavityCouplingStartTranslation h) (cavityCouplingPathTranslation h)
    (measurable_cavityCouplingStartTranslation h) (measurable_cavityCouplingPathTranslation h)
    (by ext z:1;rw [Kernel.comap_apply,Kernel.const_apply,Kernel.const_apply])
    (fun j=>cavityCoupling_reference_path_translation_kernel D _ _ h)
    (fun j Z=>cavityCouplingPathTranslation_endpoint D (q j) h Z) T

theorem measurable_treeNativePathLog (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap)
    {j:ℕ} (T : FiniteTerminalGenealogy j):
    Measurable (Function.uncurry (treeNativePathLog D μ q T)) := by
  exact measurable_treePathLogDensity _ _ _
    (fun j=>measurable_edgePathEndpoint D (q j)) (measurable_treeNativeSpinLog D μ)
    (fun j=>by
      convert (continuous_edgePathLogDensity D μ (q (j+1)) (q j)).measurable.comp
        (measurable_snd : Measurable (fun p:AnisotropicObservationState n×NativeTreePath n=>p.2)) using 1
      rfl) T

theorem cavityCoupling_shifted_physical_tree_density (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (hq : ∀j,q (j+1)≤q j)
    (h : AnisotropicDisorder n) {j:ℕ} (T : FiniteTerminalGenealogy j)
    (z : AnisotropicObservationState n):
    treeNativePathKernel D μ q T (cavityCouplingStartTranslation h z)=
      ((treeReferencePathKernel D q T z).withDensity
        (fun Z=>ENNReal.ofReal (Real.exp (treeNativePathLog D μ q T
          (cavityCouplingStartTranslation h z)
            (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z))))).map
              (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T) := by
  have hm:=measurable_cavityTreeRecordPathMap (S:=Configuration n)
    (cavityCouplingPathTranslation h) (measurable_cavityCouplingPathTranslation h) T
  have hw:Measurable (fun Z=>ENNReal.ofReal (Real.exp
      (treeNativePathLog D μ q T (cavityCouplingStartTranslation h z) Z))) :=
    (((measurable_treeNativePathLog D μ q T).comp measurable_prodMk_left).exp).ennreal_ofReal
  rw [map_withDensity_pullback _ _ hm _ hw]
  have hr:=congrArg (fun k:Kernel (AnisotropicObservationState n)
      (Records (NativeTreePath n) (Configuration n) T)=>k z)
    (cavityCoupling_reference_tree_translation_kernel D q h T)
  rw [Kernel.map_apply _ hm,Kernel.comap_apply] at hr
  rw [hr,treeNativePathKernel_exp_density D μ q hq T,
    Kernel.withDensity_apply _ ((measurable_treeNativePathLog D μ q T).exp.ennreal_ofReal)]

end HexagonPaper
