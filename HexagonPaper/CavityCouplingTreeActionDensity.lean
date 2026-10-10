module
public import HexagonPaper.CavityCouplingTreeAction

@[expose] public section

/-! Genuine translated source action RN identity relative to the native
baseline tree probability. No pointwise identification with the stopped
path log is needed on incompatible records. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup FiniteTerminalGenealogy
open scoped Topology ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem measurable_treeNativeSourceLog (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (Function.uncurry (treeNativeSourceLog D μ q T)) :=
  measurable_treePathLogDensity _ _ _ (fun j=>measurable_edgePathEndpoint D (q j))
    (measurable_treeNativeSpinLog D μ) (fun j=>measurable_edgePathSourceLog D μ (q (j+1)) (q j)) T

theorem cavityCoupling_shifted_physical_tree_source_density (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (hq : ∀j,q (j+1)≤q j)
    (h : AnisotropicDisorder n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (z : AnisotropicObservationState n) :
    treeNativePathKernel D μ q T (cavityCouplingStartTranslation h z)=
      ((treeReferencePathKernel D q T z).withDensity
        (fun Z=>ENNReal.ofReal (Real.exp (treeNativeSourceLog D μ q T
          (cavityCouplingStartTranslation h z)
            (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z))))).map
              (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T) := by
  have hm:=measurable_cavityTreeRecordPathMap (S:=Configuration n)
    (cavityCouplingPathTranslation h) (measurable_cavityCouplingPathTranslation h) T
  have hw : Measurable (fun Z=>ENNReal.ofReal (Real.exp
      (treeNativeSourceLog D μ q T (cavityCouplingStartTranslation h z) Z))) :=
    (((measurable_treeNativeSourceLog D μ q T).comp measurable_prodMk_left).exp).ennreal_ofReal
  rw [map_withDensity_pullback _ _ hm _ hw]
  have hr:=congrArg (fun k : Kernel (AnisotropicObservationState n)
      (Records (NativeTreePath n) (Configuration n) T)=>k z)
    (cavityCoupling_reference_tree_translation_kernel D q h T)
  rw [Kernel.map_apply _ hm,Kernel.comap_apply] at hr
  rw [hr,treeNativePathKernel_source_exp_density D μ q hq T,
    Kernel.withDensity_apply _ ((measurable_treeNativeSourceLog D μ q T).exp.ennreal_ofReal)]

theorem cavityCoupling_shifted_physical_tree_source_relative_density (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (hq : ∀j,q (j+1)≤q j)
    (h : AnisotropicDisorder n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (z : AnisotropicObservationState n) :
    treeNativePathKernel D μ q T (cavityCouplingStartTranslation h z)=
      ((treeNativePathKernel D μ q T z).withDensity
        (fun Z=>ENNReal.ofReal (Real.exp (
          treeNativeSourceLog D μ q T (cavityCouplingStartTranslation h z)
            (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z)-
          treeNativeSourceLog D μ q T z Z)))).map
            (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T) := by
  have hbase : Measurable (fun Z=>ENNReal.ofReal (Real.exp (treeNativeSourceLog D μ q T z Z))) :=
    (((measurable_treeNativeSourceLog D μ q T).comp measurable_prodMk_left).exp).ennreal_ofReal
  have hchange : Measurable (fun Z=>treeNativeSourceLog D μ q T
      (cavityCouplingStartTranslation h z)
        (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z)) :=
    ((measurable_treeNativeSourceLog D μ q T).comp measurable_prodMk_left).comp
      (measurable_cavityTreeRecordPathMap _ (measurable_cavityCouplingPathTranslation h) T)
  have hratio : Measurable (fun Z=>ENNReal.ofReal (Real.exp (
      treeNativeSourceLog D μ q T (cavityCouplingStartTranslation h z)
        (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z)-
      treeNativeSourceLog D μ q T z Z))) :=
    (hchange.sub ((measurable_treeNativeSourceLog D μ q T).comp measurable_prodMk_left)).exp.ennreal_ofReal
  have hrn : treeNativePathKernel D μ q T z=
      (treeReferencePathKernel D q T z).withDensity
        (fun Z=>ENNReal.ofReal (Real.exp (treeNativeSourceLog D μ q T z Z))) := by
    rw [treeNativePathKernel_source_exp_density D μ q hq T,
      Kernel.withDensity_apply _ ((measurable_treeNativeSourceLog D μ q T).exp.ennreal_ofReal)]
  rw [cavityCoupling_shifted_physical_tree_source_density D μ q hq h T z,hrn,
    ←withDensity_mul _ hbase hratio]
  congr 2
  funext Z
  dsimp only [Pi.mul_apply]
  rw [←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
  congr 2
  ring

end HexagonPaper
