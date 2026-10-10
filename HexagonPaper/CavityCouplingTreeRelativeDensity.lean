module
public import HexagonPaper.CavityCouplingTreeTransport

@[expose] public section

/-! Genuine native child-tree likelihood relative to its own baseline
probability law. The ratio is the exact difference of native actions;
absolute reference RN identities and positive exponential algebra prove
the formula without a likelihood-ratio premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup FiniteTerminalGenealogy
open scoped ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n:ℕ}

theorem cavityCoupling_shifted_physical_tree_relative_density (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (hq : ∀j,q (j+1)≤q j)
    (h : AnisotropicDisorder n) {j:ℕ} (T : FiniteTerminalGenealogy j)
    (z : AnisotropicObservationState n):
    treeNativePathKernel D μ q T (cavityCouplingStartTranslation h z)=
      ((treeNativePathKernel D μ q T z).withDensity
        (fun Z=>ENNReal.ofReal (Real.exp (
          treeNativePathLog D μ q T (cavityCouplingStartTranslation h z)
            (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z)-
          treeNativePathLog D μ q T z Z)))).map
            (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T) := by
  have hbase:Measurable (fun Z=>ENNReal.ofReal (Real.exp (treeNativePathLog D μ q T z Z))):=
    (((measurable_treeNativePathLog D μ q T).comp measurable_prodMk_left).exp).ennreal_ofReal
  have hchange:Measurable (fun Z=>treeNativePathLog D μ q T
      (cavityCouplingStartTranslation h z)
        (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z)):=
    ((measurable_treeNativePathLog D μ q T).comp measurable_prodMk_left).comp
      (measurable_cavityTreeRecordPathMap _ (measurable_cavityCouplingPathTranslation h) T)
  have hratio:Measurable (fun Z=>ENNReal.ofReal (Real.exp (
      treeNativePathLog D μ q T (cavityCouplingStartTranslation h z)
        (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z)-
      treeNativePathLog D μ q T z Z))):=
    (hchange.sub ((measurable_treeNativePathLog D μ q T).comp measurable_prodMk_left)).exp.ennreal_ofReal
  have hrn:treeNativePathKernel D μ q T z=
      (treeReferencePathKernel D q T z).withDensity
        (fun Z=>ENNReal.ofReal (Real.exp (treeNativePathLog D μ q T z Z))):=by
    rw [treeNativePathKernel_exp_density D μ q hq T,
      Kernel.withDensity_apply _ ((measurable_treeNativePathLog D μ q T).exp.ennreal_ofReal)]
  rw [cavityCoupling_shifted_physical_tree_density D μ q hq h T z,hrn,
    ←withDensity_mul _ hbase hratio]
  congr 2
  funext Z
  dsimp only [Pi.mul_apply]
  rw [←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
  congr 2
  ring

end HexagonPaper
