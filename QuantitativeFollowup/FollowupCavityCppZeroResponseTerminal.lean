module
public import QuantitativeFollowup.FollowupCavityDecouplingSpinTerminal
public import QuantitativeFollowup.ScalarMarkedSpin

@[expose] public section

/-! Exact joint terminal-spin separation at the independent cavity endpoint.
The product measure follows from the actual normalized Gibbs density. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.AT
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityTerminalGibbs_zero_product (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (g : AnisotropicDisorder (n+1))
    (x : QuantitativePaper.Field (n+1)) (σ : Configuration (n+1)) :
    gtStateGibbs (fun _ : Configuration (n+1) => 0)
      (anisotropicEnergyMap (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩)
        (anisotropicParameterPoint g x)) σ =
    gtStateGibbs (fun _ : Configuration n => 0)
      (anisotropicEnergyMap (followupCavityRestSpinModel n β ρ hβ hρ)
        (anisotropicParameterPoint (cavityRestDisorderProjection n g)
          (cavityRestFieldProjection n x))) (cavityRestConfiguration σ) *
      scalarSpinWeight (x (Fin.last n)) (σ (Fin.last n)) := by
  rw [gtStateGibbs, gtStateGibbs, followupCavityPartition_zero]
  simp only [anisotropicEnergyMap_apply, add_zero, anisotropicTerminalLinear_apply]
  rw [followupCavityHamiltonian_zero, Real.exp_add]
  have hs : (∑ b : Bool, Real.exp (x (Fin.last n) * Paper.spinSign b)) =
      2 * Real.cosh (x (Fin.last n)) := by
    simp only [Fintype.sum_bool, Paper.spinSign, Bool.false_eq_true, ite_false, ite_true,
      mul_neg_one, mul_one]
    rw [Real.cosh_eq]
    ring
  rw [hs]
  simp only [scalarSpinWeight, div_eq_mul_inv, mul_inv_rev]
  rw [mul_comm (Paper.spinSign (σ (Fin.last n))) (x (Fin.last n))]
  ring

theorem cavityTerminalSpinKernel_zero_product (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (g : AnisotropicDisorder (n+1))
    (x : QuantitativePaper.Field (n+1)) :
    (anisotropicTerminalSpinKernel
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩)
      (anisotropicParameterPoint g x)).map (cavitySpinSplitEquiv n) =
    (anisotropicTerminalSpinKernel (followupCavityRestSpinModel n β ρ hβ hρ)
      (anisotropicParameterPoint (cavityRestDisorderProjection n g)
        (cavityRestFieldProjection n x))).prod (scalarSpinLaw (x (Fin.last n))) := by
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton z)]
  have hp : (cavitySpinSplitEquiv n) ⁻¹' {z} = {(cavitySpinSplitEquiv n).symm z} := by
    ext σ
    simp only [mem_preimage, mem_singleton_iff]
    exact (cavitySpinSplitEquiv n).eq_symm_apply.symm
  rw [hp]
  change finiteStateGibbsKernel _ _ {(cavitySpinSplitEquiv n).symm z} = _
  have hfst : cavityRestConfiguration ((cavitySpinSplitEquiv n).symm z) = z.1 := by
    simpa only [cavitySpinSplitEquiv_fst] using
      congrArg (fun z : Configuration n × Bool => z.1) ((cavitySpinSplitEquiv n).apply_symm_apply z)
  have hsnd : (cavitySpinSplitEquiv n).symm z (Fin.last n) = z.2 := by
    simpa only [cavitySpinSplitEquiv_snd] using
      congrArg (fun z : Configuration n × Bool => z.2) ((cavitySpinSplitEquiv n).apply_symm_apply z)
  rw [finiteStateGibbsKernel_singleton, cavityTerminalGibbs_zero_product, hfst, hsnd]
  rw [←singleton_prod_singleton, Measure.prod_prod]
  change ENNReal.ofReal (_ * _) = finiteStateGibbsKernel _ _ {z.1} *
    (scalarSpinPMF _).toMeasure {z.2}
  rw [finiteStateGibbsKernel_singleton, PMF.toMeasure_apply_singleton,
    scalarSpinPMF, PMF.ofFintype_apply,
    ENNReal.ofReal_mul (gtStateGibbs_nonneg _ _ _)]
  exact measurableSet_singleton _

theorem cavityTerminalJointFeature_zero (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (g : AnisotropicDisorder (n+1))
    (x : QuantitativePaper.Field (n+1)) (f : Configuration n → ℝ) (b : Bool → ℝ) :
    anisotropicTerminalFeatureMean
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩)
      (fun σ => f (cavityRestConfiguration σ) * b (σ (Fin.last n)))
      (anisotropicParameterPoint g x) =
    anisotropicTerminalFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) f
      (anisotropicParameterPoint (cavityRestDisorderProjection n g)
        (cavityRestFieldProjection n x)) * (∫ e, b e ∂scalarSpinLaw (x (Fin.last n))) := by
  have hm : Measurable (fun z : Configuration n × Bool => f z.1 * b z.2) :=
    measurable_of_finite _
  have hi := integral_map
    (μ := anisotropicTerminalSpinKernel
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩)
      (anisotropicParameterPoint g x))
    (measurable_of_finite (cavitySpinSplitEquiv n)).aemeasurable
    hm.aestronglyMeasurable
  rw [cavityTerminalSpinKernel_zero_product] at hi
  rw [integral_prod_mul] at hi
  simpa only [anisotropicTerminalFeatureMean, Function.comp_def,
    cavitySpinSplitEquiv_fst, cavitySpinSplitEquiv_snd] using hi.symm

theorem cavityTerminalIncidentFeature_zero (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (g : AnisotropicDisorder (n+1))
    (x : QuantitativePaper.Field (n+1)) (f : Configuration n → ℝ) :
    anisotropicTerminalFeatureMean
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩)
      (fun σ => f (cavityRestConfiguration σ) * Paper.spinSign (σ (Fin.last n)))
      (anisotropicParameterPoint g x) =
    anisotropicTerminalFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) f
      (anisotropicParameterPoint (cavityRestDisorderProjection n g)
        (cavityRestFieldProjection n x)) * Real.tanh (x (Fin.last n)) := by
  rw [cavityTerminalJointFeature_zero, integral_scalarSpinLaw_sign]

end QuantitativeFollowup
