module
public import QuantitativePaper.VectorAffineControl

@[expose] public section

/-! Genuine dominated differentiation of the actual expected fixed-control
probability variation, including bounded initial weights. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem measurable_vectorAffineControlPayoff (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (lam : ℝ) : Measurable (vectorAffineControlPayoff μ ν β t A lam) := by
  let c := (1-t)*β^2
  have hX := (measurable_vectorControlledState c μ A hA).of_uncurry_left (x := 1)
  have hY := (measurable_vectorControlledState c ν A hA).of_uncurry_left (x := 1)
  have hW := hX.add ((hY.sub hX).const_smul lam)
  have hF := (contDiff_vectorTerminalPotential_joint n β t (1 : ℕ)).continuous.measurable.comp
    (measurable_fst.prodMk hW)
  have hμ := measurable_vectorParisiControlIntegratedCost c μ A hA
  have hν := measurable_vectorParisiControlIntegratedCost c ν A hA
  exact hF.sub (hμ.add ((hν.sub hμ).const_mul lam))

theorem measurable_vectorAffineControlDerivative (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (lam : ℝ) : Measurable (vectorAffineControlDerivative μ ν β t A lam) := by
  let c := (1-t)*β^2
  have hX := (measurable_vectorControlledState c μ A hA).of_uncurry_left (x := 1)
  have hY := (measurable_vectorControlledState c ν A hA).of_uncurry_left (x := 1)
  have hW := hX.add ((hY.sub hX).const_smul lam)
  have hG := (continuous_vectorTerminalGradient (n := n) β t).measurable.comp
    (measurable_fst.prodMk hW)
  exact (hG.inner (hY.sub hX)).sub
    ((measurable_vectorParisiControlIntegratedCost c ν A hA).sub
      (measurable_vectorParisiControlIntegratedCost c μ A hA))

theorem integrable_vectorAffineControlDerivative (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (lam : ℝ) : Integrable (vectorAffineControlDerivative μ ν β t A lam)
      (vectorDisorderBrownianMeasure n) := by
  apply (integrable_const (3*|(1-t)*β^2| *(n : ℝ))).mono'
    (measurable_vectorAffineControlDerivative μ ν β t A hA lam).aestronglyMeasurable
  exact Eventually.of_forall (norm_vectorAffineControlDerivative_le μ ν β t A hA lam)

theorem vectorWeightedParisiControlObjective_hasDerivWithinAt_mix
    (μ ν : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (Z : VectorDisorderBrownianSample n → ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖ ≤ C) :
    HasDerivWithinAt (fun lam => vectorWeightedParisiControlObjective (Paper.parisiMix μ ν lam) β t A Z)
      (∫sample,Z sample*vectorAffineControlDerivative μ ν β t A 0 sample
        ∂vectorDisorderBrownianMeasure n) (Icc (0 : ℝ) 1) 0 := by
  have hi : Integrable (fun sample => Z sample*vectorAffineControlPayoff μ ν β t A 0 sample)
      (vectorDisorderBrownianMeasure n) := by
    simpa only [vectorAffineControlPayoff,zero_smul,add_zero,zero_mul] using
      integrable_vectorWeightedParisiControlPayoff μ β t ht A hA Z hZ C hC
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun lam sample => Z sample*vectorAffineControlPayoff μ ν β t A lam sample)
    (F' := fun lam sample => Z sample*vectorAffineControlDerivative μ ν β t A lam sample)
    (bound := fun _ => (C : ℝ)*(3*|(1-t)*β^2| *(n : ℝ)))
    (s := (univ : Set ℝ)) (by simp)
    (Eventually.of_forall (fun lam => (hZ.mul (measurable_vectorAffineControlPayoff μ ν β t A hA lam)).aestronglyMeasurable))
    hi (hZ.mul (measurable_vectorAffineControlDerivative μ ν β t A hA 0)).aestronglyMeasurable
    (Eventually.of_forall (fun sample lam _ => by
      rw [norm_mul]
      exact mul_le_mul (hC sample) (norm_vectorAffineControlDerivative_le μ ν β t A hA lam sample)
        (norm_nonneg _) C.coe_nonneg))
    (integrable_const _)
    (Eventually.of_forall (fun sample lam _ =>
      (hasDerivAt_vectorAffineControlPayoff μ ν β t A lam sample).const_mul (Z sample)))).2
  apply hd.hasDerivWithinAt.congr_of_mem
  · intro lam hlam
    unfold vectorWeightedParisiControlObjective
    apply integral_congr_ae
    exact Eventually.of_forall (fun sample => by
      dsimp only
      rw [vectorAffineControlPayoff_eq_mix μ ν β t lam hlam A hA])
  · exact ⟨le_rfl,zero_le_one⟩

end QuantitativePaper
