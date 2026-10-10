module
public import QuantitativeFollowup.AnisotropicDyadicLawAgreement
public import QuantitativeFollowup.FollowupCavityPathNormalization

@[expose] public section

/-! The actual finite path normalizer is the genuine finite disorder
partition. The arbitrary-profile root normalizer agrees exactly on each
constructed dyadic finite law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem anisotropicFiniteOuterPartition_eq_cavityPathNormalizer
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n) :
    anisotropicFiniteOuterPartition D s a=cavityPathNormalizer D s a i (k+2) (D.variance i) := by
  unfold cavityPathNormalizer
  rw [anisotropicReplaceVariance_self]
  unfold finiteCascadeTreeGaussianNormalizer anisotropicFiniteOuterPartition
  rw [finiteStateGaussianRawKernel_apply,integral_map (by fun_prop)
    (by
      have h:=((contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
        (cavityFiniteEnergyInput D s) (k+2)).continuous.measurable.const_mul a).exp
      exact h.aestronglyMeasurable)]
  apply integral_congr_ae
  exact .of_forall fun g=>by
    simp only [zero_add,anisotropicFiniteFieldPotential,anisotropicParameterPoint,
      anisotropicRootEnergyMap,ContinuousLinearMap.comp_apply,anisotropicFinitePotential,cavityFiniteEnergyInput]
    rfl

theorem anisotropicMeasureOuterPartition_grid_eq_cavityPathNormalizer
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (j : ℕ) (a : ℝ) (i : Fin n) :
    anisotropicMeasureOuterPartition D (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) a=
      cavityPathNormalizer D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a i
        (vectorDyadicIndex j+3) (D.variance i) := by
  rw [anisotropicMeasureOuterPartition_grid_eq_finite,anisotropicFiniteOuterPartition_eq_cavityPathNormalizer]

end QuantitativeFollowup
