module
public import FourPapersCommon.ParisiForkRestart
public import FourPapersCommon.BrownianFutureForkLaw
public import FourPapersCommon.IndependentNoiseKernel

@[expose] public section

/-! Exact physical joint and fork endpoint laws for the actual diffusion,
with the fresh-noise kernel constructed from the proved Picard restart. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1200000

def parisiPhysicalRestartKernel (β : ℝ) (μ : ParisiMeasure)
    (a b : Paper.Overlap) (hab : (a : ℝ)≤b) : Kernel ℝ ℝ :=
  independentNoiseKernel canonicalWienerMeasure (parisiPhysicalRestartEndpoint β μ a b hab)

theorem isMarkovKernel_parisiPhysicalRestartKernel (β : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) (a b : Paper.Overlap) (hab : (a : ℝ)≤b) :
    IsMarkovKernel (parisiPhysicalRestartKernel β μ a b hab) :=
  isMarkovKernel_independentNoiseKernel _ _
    (measurable_parisiPhysicalRestartEndpoint β hβ μ a b hab)

theorem parisiPhysicalSplitState_joint_law (β h : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) (a b : Paper.Overlap) (hab : (a : ℝ)≤b) :
    canonicalBrownianMeasure.map (fun sample=>(parisiPhysicalSplitState β h μ a sample,
      parisiPhysicalSplitState β h μ b sample))=
      (canonicalBrownianMeasure.map (parisiPhysicalSplitState β h μ a)) ⊗ₘ
        parisiPhysicalRestartKernel β μ a b hab := by
  have hY:=measurable_parisiPhysicalSplitState_past β h hβ μ a
  have hYg:=hY.mono (canonicalBrownianFiltration.le _) le_rfl
  have hF:=measurable_canonicalFutureBrownianPath (a : ℝ).toNNReal
  have hf:=measurable_parisiPhysicalRestartEndpoint β hβ μ a b hab
  letI : IsProbabilityMeasure (canonicalBrownianMeasure.map (parisiPhysicalSplitState β h μ a)) :=
    (Measure.isProbabilityMeasure_map_iff hYg.aemeasurable).mpr inferInstance
  calc
    _ = (canonicalBrownianMeasure.map (fun sample=>(parisiPhysicalSplitState β h μ a sample,
        canonicalFutureBrownianPath (a : ℝ).toNNReal sample))).map
        (fun z=>(z.1,parisiPhysicalRestartEndpoint β μ a b hab z)) := by
      rw [Measure.map_map (measurable_fst.prodMk hf) (hYg.prodMk hF)]
      congr 1
      funext sample
      simp only [Function.comp_def,parisiPhysicalSplitState_restart β h μ a b hab]
    _ = _ := by
      rw [canonicalFutureBrownianPath_joint_law _ _ hY]
      exact independentNoiseKernel_joint_law _ _ _ hf

theorem parisiPhysicalForkState_joint_law (β h : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) (a b : Paper.Overlap) (hab : (a : ℝ)≤b) :
    brownianPairMeasure.map (fun sample=>(parisiPhysicalSplitState β h μ b sample.1,
      parisiNoiseStatePath β h μ (forkBrownianPath (a : ℝ).toNNReal sample) b))=
      (parisiPhysicalRestartKernel β μ a b hab ×ₖ parisiPhysicalRestartKernel β μ a b hab) ∘ₘ
        canonicalBrownianMeasure.map (parisiPhysicalSplitState β h μ a) := by
  have hY:=measurable_parisiPhysicalSplitState_past β h hβ μ a
  have hYg:=hY.mono (canonicalBrownianFiltration.le _) le_rfl
  have hF:=measurable_canonicalFutureBrownianPath (a : ℝ).toNNReal
  have hf:=measurable_parisiPhysicalRestartEndpoint β hβ μ a b hab
  have htriple : Measurable (fun sample : BrownianPair=>(parisiPhysicalSplitState β h μ a sample.1,
      (canonicalFutureBrownianPath (a : ℝ).toNNReal sample.1,
        canonicalFutureBrownianPath (a : ℝ).toNNReal sample.2))) :=
    (hYg.comp measurable_fst).prodMk
      ((hF.comp measurable_fst).prodMk (hF.comp measurable_snd))
  have hp : Measurable (fun z : ℝ×(C(Paper.Overlap,ℝ)×C(Paper.Overlap,ℝ))=>
      (parisiPhysicalRestartEndpoint β μ a b hab (z.1,z.2.1),
        parisiPhysicalRestartEndpoint β μ a b hab (z.1,z.2.2))) :=
    (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (hf.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  letI : IsProbabilityMeasure (canonicalBrownianMeasure.map (parisiPhysicalSplitState β h μ a)) :=
    (Measure.isProbabilityMeasure_map_iff hYg.aemeasurable).mpr inferInstance
  calc
    _ = (brownianPairMeasure.map (fun sample=>(parisiPhysicalSplitState β h μ a sample.1,
        (canonicalFutureBrownianPath (a : ℝ).toNNReal sample.1,
          canonicalFutureBrownianPath (a : ℝ).toNNReal sample.2)))).map
        (fun z=>(parisiPhysicalRestartEndpoint β μ a b hab (z.1,z.2.1),
          parisiPhysicalRestartEndpoint β μ a b hab (z.1,z.2.2))) := by
      rw [Measure.map_map hp htriple]
      congr 1
      funext sample
      dsimp only [Function.comp_def]
      rw [parisiPhysicalSplitState_restart β h μ a b hab,
        parisiPhysicalForkState_restart β h μ a b hab]
    _ = _ := by
      rw [brownianFutureFork_triple_law _ _ hY]
      exact independentNoiseKernel_two_branch_law _ _ _ hf

end FourPapersCommon
