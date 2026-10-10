module
public import FourPapersCommon.ParisiForkRestart
public import FourPapersCommon.IndependentNoiseKernel
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! The genuine Markov transition of the constructed scalar diffusion.
Fresh future Wiener noise is independent of the entire original past;
pathwise Picard uniqueness identifies its restarted state with the future
state. No transition or conditional-expectation conclusion is a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def scalarTransitionKernel (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) : Kernel ℝ ℝ :=
  independentNoiseKernel canonicalWienerMeasure (parisiPhysicalRestartEndpoint β μ r q hrq)

theorem scalarTransitionKernel_isMarkov (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) :
    IsMarkovKernel (scalarTransitionKernel β μ r q hrq) :=
  isMarkovKernel_independentNoiseKernel _ _
    (measurable_parisiPhysicalRestartEndpoint β hβ μ r q hrq)

def scalarTransitionExpectation (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ W, F (parisiPhysicalRestartEndpoint β μ r q hrq (x,W)) ∂canonicalWienerMeasure

theorem measurable_scalarTransitionExpectation (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q)
    (F : ℝ → ℝ) (hF : Measurable F) :
    Measurable (scalarTransitionExpectation β μ r q hrq F) := by
  have hm : Measurable (fun z : ℝ×C(Paper.Overlap,ℝ) =>
      F (parisiPhysicalRestartEndpoint β μ r q hrq z)) :=
    hF.comp (measurable_parisiPhysicalRestartEndpoint β hβ μ r q hrq)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem norm_scalarTransitionExpectation_le (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) (F : ℝ → ℝ)
    (L : ℝ) (hF : ∀ x, ‖F x‖ ≤ L) (x : ℝ) :
    ‖scalarTransitionExpectation β μ r q hrq F x‖ ≤ L := by
  simpa only [scalarTransitionExpectation,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := canonicalWienerMeasure)
      (.of_forall fun W => hF (parisiPhysicalRestartEndpoint β μ r q hrq (x,W)))

/-- Weighted actual Markov identity for every bounded whole-past weight. -/
theorem scalarTransition_weighted_expectation (β h : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q)
    (F : ℝ → ℝ) (hF : Measurable F) (L : ℝ) (hbF : ∀ x, ‖F x‖ ≤ L)
    (Z : Paper.BrownianSample → ℝ)
    (hZ : Measurable[canonicalBrownianFiltration (r : ℝ).toNNReal] Z)
    (K : ℝ) (hbZ : ∀ ω, ‖Z ω‖ ≤ K) :
    (∫ ω, Z ω * F (parisiPhysicalSplitState β h μ q ω) ∂canonicalBrownianMeasure) =
      ∫ ω, Z ω * scalarTransitionExpectation β μ r q hrq F
        (parisiPhysicalSplitState β h μ r ω) ∂canonicalBrownianMeasure := by
  let Y : Paper.BrownianSample → ℝ×ℝ := fun ω => (Z ω,parisiPhysicalSplitState β h μ r ω)
  have hY : Measurable[canonicalBrownianFiltration (r : ℝ).toNNReal] Y :=
    hZ.prodMk (measurable_parisiPhysicalSplitState_past β h hβ μ r)
  have hYm : Measurable Y := hY.mono (canonicalBrownianFiltration.le _) le_rfl
  let ν := canonicalBrownianMeasure.map Y
  let H : (ℝ×ℝ)×C(Paper.Overlap,ℝ) → ℝ := fun z =>
    z.1.1 * F (parisiPhysicalRestartEndpoint β μ r q hrq (z.1.2,z.2))
  have hHm : Measurable H := (measurable_fst.comp measurable_fst).mul
    (hF.comp ((measurable_parisiPhysicalRestartEndpoint β hβ μ r q hrq).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have hZm : Measurable Z := hZ.mono (canonicalBrownianFiltration.le _) le_rfl
  have hZi : Integrable Z canonicalBrownianMeasure :=
    (integrable_const K).mono' hZm.aestronglyMeasurable (.of_forall hbZ)
  have hνi : Integrable (fun z : ℝ×ℝ => z.1) ν := by
    exact (integrable_map_measure measurable_fst.aestronglyMeasurable hYm.aemeasurable).2 hZi
  have hHi : Integrable H (ν.prod canonicalWienerMeasure) := by
    apply (hνi.comp_fst canonicalWienerMeasure).mul_bdd (c := L)
      (hF.comp ((measurable_parisiPhysicalRestartEndpoint β hβ μ r q hrq).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).aestronglyMeasurable
    exact .of_forall fun z => hbF _
  have hlaw := canonicalFutureBrownianPath_joint_law (r : ℝ).toNNReal Y hY
  have hpair : Measurable (fun ω => (Y ω,canonicalFutureBrownianPath (r : ℝ).toNNReal ω)) :=
    hYm.prodMk (measurable_canonicalFutureBrownianPath _)
  have he := integral_map (μ := canonicalBrownianMeasure) hpair.aemeasurable hHm.aestronglyMeasurable
  rw [hlaw] at he
  calc
    _ = ∫ ω, H (Y ω,canonicalFutureBrownianPath (r : ℝ).toNNReal ω)
        ∂canonicalBrownianMeasure := by
      apply integral_congr_ae
      exact .of_forall fun ω => by
        dsimp only [H,Y]
        rw [parisiPhysicalSplitState_restart β h μ r q hrq ω]
    _ = ∫ z, H z ∂ν.prod canonicalWienerMeasure := he.symm
    _ = ∫ z : ℝ×ℝ, z.1 * scalarTransitionExpectation β μ r q hrq F z.2 ∂ν := by
      rw [integral_prod _ hHi]
      apply integral_congr_ae
      exact .of_forall fun z => by
        dsimp only [H]
        rw [integral_const_mul]
        rfl
    _ = _ := integral_map hYm.aemeasurable
      (measurable_fst.mul ((measurable_scalarTransitionExpectation β hβ μ r q hrq F hF).comp
        measurable_snd)).aestronglyMeasurable

end QuantitativeFollowup
