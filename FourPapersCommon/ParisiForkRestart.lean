module
public import FourPapersCommon.ParisiNoiseRestart
public import FourPapersCommon.CanonicalBrownianFuture
public import FourPapersCommon.MixedForkPrefix
public import FRSB.ConstantMassLaw

@[expose] public section

/-! Pointwise physical restart formulas for both actual Brownian branches,
sharing exactly the same sampled initial state at the split. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1200000

def parisiPhysicalSplitState (β h : ℝ) (μ : ParisiMeasure) (a : Paper.Overlap)
    (sample : Paper.BrownianSample) : ℝ :=
  parisiNoiseStatePath β h μ (canonicalBrownianPath sample) a

theorem measurable_parisiPhysicalSplitState_past (β h : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) (a : Paper.Overlap) :
    Measurable[canonicalBrownianFiltration (a : ℝ).toNNReal]
      (parisiPhysicalSplitState β h μ a) := by
  have he : parisiPhysicalSplitState β h μ a=
      selectedParisiItoState β h hβ μ (a : ℝ).toNNReal := by
    funext sample
    rw [parisiPhysicalSplitState,parisiNoiseStatePath_canonical β h hβ]
    have hi:=selectedParisiItoState_eq β h hβ μ
      (t:=(a : ℝ).toNNReal) (by rw [Real.coe_toNNReal _ a.property.1]; exact a.property.2) sample
    rw [Real.coe_toNNReal _ a.property.1] at hi
    exact hi.symm
  rw [he]
  exact (FRSB.stronglyAdapted_selectedParisiState β h hβ μ _).measurable

def parisiPhysicalRestartEndpoint (β : ℝ) (μ : ParisiMeasure)
    (a b : Paper.Overlap) (hab : (a : ℝ)≤b) (z : ℝ×C(Paper.Overlap,ℝ)) : ℝ :=
  parisiRestartNoiseStatePath β z.1 μ a a.property.1 z.2 (parisiElapsedOverlap a b hab)

theorem measurable_parisiPhysicalRestartEndpoint (β : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) (a b : Paper.Overlap) (hab : (a : ℝ)≤b) :
    Measurable (parisiPhysicalRestartEndpoint β μ a b hab) := by
  have he : Measurable (fun W : C(Paper.Overlap,ℝ)=>W (parisiElapsedOverlap a b hab)) :=
    (ProbabilityTheory.ContinuousMap.measurable_iff_eval
      (fun W : C(Paper.Overlap,ℝ)=>W)).mp measurable_id _
  exact he.comp (measurable_parisiRestartNoiseStatePath β hβ μ a a.property.1)

theorem parisiPhysicalSplitState_restart (β h : ℝ) (μ : ParisiMeasure)
    (a b : Paper.Overlap) (hab : (a : ℝ)≤b) (sample : Paper.BrownianSample) :
    parisiPhysicalSplitState β h μ b sample=
      parisiPhysicalRestartEndpoint β μ a b hab
        (parisiPhysicalSplitState β h μ a sample,canonicalFutureBrownianPath (a : ℝ).toNNReal sample) := by
  apply parisiNoiseStatePath_restart
  intro s hs
  change canonicalBrownian ((a : ℝ).toNNReal+(s : ℝ).toNNReal) sample-
      canonicalBrownian (a : ℝ).toNNReal sample=
    canonicalBrownian ((a : ℝ)+(s : ℝ)).toNNReal sample-
      canonicalBrownian (a : ℝ).toNNReal sample
  rw [Real.toNNReal_add a.property.1 s.property.1]

theorem parisiPhysicalForkState_restart (β h : ℝ) (μ : ParisiMeasure)
    (a b : Paper.Overlap) (hab : (a : ℝ)≤b) (sample : BrownianPair) :
    parisiNoiseStatePath β h μ (forkBrownianPath (a : ℝ).toNNReal sample) b=
      parisiPhysicalRestartEndpoint β μ a b hab
        (parisiPhysicalSplitState β h μ a sample.1,
          canonicalFutureBrownianPath (a : ℝ).toNNReal sample.2) := by
  have hstart : parisiNoiseStatePath β h μ (forkBrownianPath (a : ℝ).toNNReal sample) a=
      parisiPhysicalSplitState β h μ a sample.1 := by
    apply parisiNoiseStatePath_causal β h μ _ _ a
    · intro t ht
      exact forkBrownianPath_before _ _ _ (Real.toNNReal_mono ht)
    · exact le_rfl
  have he:=parisiNoiseStatePath_restart β h μ a b hab
    (forkBrownianPath (a : ℝ).toNNReal sample)
    (canonicalFutureBrownianPath (a : ℝ).toNNReal sample.2) (by
      intro s hs
      change canonicalBrownian ((a : ℝ).toNNReal+(s : ℝ).toNNReal) sample.2-
          canonicalBrownian (a : ℝ).toNNReal sample.2=
        forkBrownian (a : ℝ).toNNReal ((a : ℝ)+(s : ℝ)).toNNReal sample-
          forkBrownian (a : ℝ).toNNReal (a : ℝ).toNNReal sample
      rw [Real.toNNReal_add a.property.1 s.property.1,
        forkBrownian_after _ _ (le_add_of_nonneg_right (by positivity)) sample,
        forkBrownian_before _ _ le_rfl sample]
      ring)
  rw [hstart] at he
  exact he

end FourPapersCommon
