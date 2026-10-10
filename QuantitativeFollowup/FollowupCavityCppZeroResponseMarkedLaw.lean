module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseTerminal
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProduct
public import QuantitativeFollowup.FollowupCavityDecouplingCovariance
public import QuantitativeFollowup.ScalarFiniteMarkedDensity
public import Mathlib.Probability.Kernel.Composition.Lemmas

@[expose] public section

/-! Exact scalar/rest product law of the whole native driving sample and
the actual terminal Gibbs mark at zero incident coupling. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityZeroMarkedSampleSplit (n : ℕ)
    (p : AnisotropicDisorderBrownianSample (n+1) × Configuration (n+1)) :
    (AnisotropicDisorderBrownianSample n × Configuration n) × (Paper.BrownianSample × Bool) :=
  ((cavityRestSampleProjection n p.1, cavityRestConfiguration p.2),
    (p.1.2 (Fin.last n), p.2 (Fin.last n)))

theorem measurable_cavityZeroMarkedSampleSplit (n : ℕ) :
    Measurable (cavityZeroMarkedSampleSplit n) := by
  have hs := measurable_cavityZeroSampleSplit n
  exact ((hs.fst.comp measurable_fst).prodMk
    ((measurable_of_finite cavityRestConfiguration).comp measurable_snd)).prodMk
    ((hs.snd.comp measurable_fst).prodMk ((measurable_pi_apply (Fin.last n)).comp measurable_snd))

theorem cavityMeasureTerminalKernel_zero_product (μ : Paper.ParisiMeasure) (n : ℕ)
    (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) :
    (anisotropicMeasureTerminalKernel
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩) μ).map (cavitySpinSplitEquiv n) =
      ((anisotropicMeasureTerminalKernel (followupCavityRestSpinModel n β ρ hβ hρ) μ) ∥ₖ
        (scalarTerminalSpinKernel (followupCavityScalarBeta n β ρ)
          (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ)).comap
            (cavityZeroSampleSplit n) (measurable_cavityZeroSampleSplit n) := by
  ext p : 1
  rw [Kernel.map_apply _ (measurable_of_finite _), Kernel.comap_apply, Kernel.parallelComp_apply]
  let D := followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩
  let R := followupCavityRestSpinModel n β ρ hβ hρ
  let X := anisotropicMeasureState D μ 1 p
  have hp : anisotropicProcessParameter D μ 1 p = anisotropicParameterPoint p.1 X := by
    rw [anisotropicProcessParameter, anisotropicDisorderInjection_apply, ←anisotropicParameterPoint_field]
    norm_num [X]
  change (anisotropicTerminalSpinKernel D (anisotropicProcessParameter D μ 1 p)).map
    (cavitySpinSplitEquiv n) = _
  rw [hp, cavityTerminalSpinKernel_zero_product]
  have hr : anisotropicParameterPoint (cavityRestDisorderProjection n p.1)
      (cavityRestFieldProjection n X) = anisotropicProcessParameter R μ 1 (cavityRestSampleProjection n p) := by
    rw [←cavityRestParameterProjection_point, ←hp]
    exact cavityRestProcessParameter_zero μ n β ρ hβ hρ 1 p
  have hl : X (Fin.last n) = parisiPhysicalSplitState (followupCavityScalarBeta n β ρ) 0 μ 1
      (p.2 (Fin.last n)) := by
    dsimp only [X, D]
    rw [cavityLastMeasureState_zero μ n β ρ hβ hρ 1 (by constructor <;> norm_num) p,
      parisiPhysicalSplitState_eq_selected _
        (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ 1,
      Paper.selectedParisiItoState_eq _ _ (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' _ (by norm_num)]
    norm_num
  rw [hr, hl]
  rfl

theorem cavityZeroMarkedSampleSplit_law (μ : Paper.ParisiMeasure) (n : ℕ)
    (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (a : ℝ) :
    (anisotropicMeasureSpinPathLaw
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩) μ a).map
        (cavityZeroMarkedSampleSplit n) =
      (anisotropicMeasureSpinPathLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a).prod
        (scalarMarkedSpinLaw (followupCavityScalarBeta n β ρ)
          (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ) := by
  let D := followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩
  let κ := (anisotropicMeasureTerminalKernel (followupCavityRestSpinModel n β ρ hβ hρ) μ) ∥ₖ
    scalarTerminalSpinKernel (followupCavityScalarBeta n β ρ)
      (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ
  let h := fun z : (AnisotropicDisorderBrownianSample n × Paper.BrownianSample) ×
      (Configuration n × Bool) => ((z.1.1,z.2.1),(z.1.2,z.2.2))
  have he : cavityZeroMarkedSampleSplit n = h ∘
      (fun z => (cavityZeroSampleSplit n z.1, z.2)) ∘ Prod.map id (cavitySpinSplitEquiv n) := by
    funext z
    change ((cavityRestSampleProjection n z.1,cavityRestConfiguration z.2),
      (z.1.2 (Fin.last n),z.2 (Fin.last n))) =
      ((cavityRestSampleProjection n z.1,(cavitySpinSplitEquiv n z.2).1),
        (z.1.2 (Fin.last n),(cavitySpinSplitEquiv n z.2).2))
    rw [cavitySpinSplitEquiv_fst,cavitySpinSplitEquiv_snd]
  have hB : Measurable (fun z : AnisotropicDisorderBrownianSample (n+1) ×
      (Configuration n × Bool) => (cavityZeroSampleSplit n z.1, z.2)) :=
    ((measurable_cavityZeroSampleSplit n).comp measurable_fst).prodMk measurable_snd
  have hC : Measurable (Prod.map (id : AnisotropicDisorderBrownianSample (n+1) → _)
      (cavitySpinSplitEquiv n)) :=
    measurable_id.prodMap (measurable_of_finite _)
  rw [he, ←Measure.map_map (by fun_prop) (hB.comp hC), ←Measure.map_map hB hC]
  unfold anisotropicMeasureSpinPathLaw
  rw [←Measure.compProd_map (measurable_of_finite _), cavityMeasureTerminalKernel_zero_product,
    compProd_comap_map_history, cavityZeroSampleSplit_law,
    cavityIndependentMarkedProduct]
  rfl

end QuantitativeFollowup
