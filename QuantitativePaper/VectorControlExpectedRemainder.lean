module
public import QuantitativePaper.VectorControlRemainder

@[expose] public section

/-! The actual weighted control objective has a uniform quadratic mixing
remainder. All payoff and derivative integrability is discharged. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorWeightedParisiControlObjective_eq_affine (μ ν : Paper.ParisiMeasure)
    (β t lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (Z : VectorDisorderBrownianSample n → ℝ) :
    vectorWeightedParisiControlObjective (Paper.parisiMix μ ν lam) β t A Z =
      ∫sample,Z sample*vectorAffineControlPayoff μ ν β t A lam sample ∂vectorDisorderBrownianMeasure n := by
  unfold vectorWeightedParisiControlObjective
  apply integral_congr_ae
  exact Eventually.of_forall (fun sample => by
    dsimp only; rw [vectorAffineControlPayoff_eq_mix μ ν β t lam hlam A hA])

theorem vectorWeightedParisiControlObjective_mix_remainder_le
    (μ ν : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (Z : VectorDisorderBrownianSample n → ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖ ≤ C)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) :
    ‖vectorWeightedParisiControlObjective (Paper.parisiMix μ ν lam) β t A Z-
      vectorWeightedParisiControlObjective μ β t A Z-
      lam*(∫sample,Z sample*vectorAffineControlDerivative μ ν β t A 0 sample
        ∂vectorDisorderBrownianMeasure n)‖ ≤
      (C : ℝ)*(4*(n : ℝ)^2*((1-t)*β^2)^2)*lam^2 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl,zero_le_one⟩
  have hi (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
      Integrable (fun sample => Z sample*vectorAffineControlPayoff μ ν β t A a sample)
        (vectorDisorderBrownianMeasure n) := by
    have hh := integrable_vectorWeightedParisiControlPayoff (Paper.parisiMix μ ν a) β t ht A hA Z hZ C hC
    have he : (fun sample => Z sample*vectorAffineControlPayoff μ ν β t A a sample) =
        (fun sample => Z sample*(vectorTerminalPotential n β t sample.1
          (vectorControlledState ((1-t)*β^2) (Paper.parisiMix μ ν a) A 1 sample)-
          vectorParisiControlIntegratedCost ((1-t)*β^2) (Paper.parisiMix μ ν a) A sample)) := by
      funext sample; rw [vectorAffineControlPayoff_eq_mix μ ν β t a ha A hA]
    rw [he]; exact hh
  have hid := (integrable_vectorAffineControlDerivative μ ν β t A hA 0).bdd_mul
    hZ.aestronglyMeasurable (Eventually.of_forall hC)
  have he1 := integral_sub (hi lam hlam) (hi 0 h0)
  have he2 := integral_sub ((hi lam hlam).sub (hi 0 h0)) (hid.const_mul lam)
  simp only [Pi.sub_apply,integral_const_mul] at he1 he2
  rw [he1] at he2
  have he0 := vectorWeightedParisiControlObjective_eq_affine μ ν β t 0 h0 A hA Z
  simp only [Paper.parisiMix_zero] at he0
  rw [vectorWeightedParisiControlObjective_eq_affine μ ν β t lam hlam A hA,he0,← he2]
  have hh := norm_integral_le_of_norm_le_const (μ := vectorDisorderBrownianMeasure n)
    (C := (C : ℝ)*(4*(n : ℝ)^2*((1-t)*β^2)^2)*lam^2)
    (f := fun sample => Z sample*vectorAffineControlPayoff μ ν β t A lam sample-
      Z sample*vectorAffineControlPayoff μ ν β t A 0 sample-
      lam*(Z sample*vectorAffineControlDerivative μ ν β t A 0 sample))
    (Eventually.of_forall (fun sample => by
      rw [show Z sample*vectorAffineControlPayoff μ ν β t A lam sample-
        Z sample*vectorAffineControlPayoff μ ν β t A 0 sample-
        lam*(Z sample*vectorAffineControlDerivative μ ν β t A 0 sample) =
        Z sample*(vectorAffineControlPayoff μ ν β t A lam sample-
          vectorAffineControlPayoff μ ν β t A 0 sample-
          lam*vectorAffineControlDerivative μ ν β t A 0 sample) from by ring,norm_mul]
      exact (mul_le_mul (hC sample)
        (vectorAffineControlPayoff_remainder_le μ ν β t A hA lam hlam.1 sample)
        (norm_nonneg _) C.coe_nonneg).trans_eq (by ring)))
  simpa only [probReal_univ,mul_one] using hh

end QuantitativePaper
