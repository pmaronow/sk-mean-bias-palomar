module
public import QuantitativePaper.VectorControlMix
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-! Actual affine control extensions for probability-measure differentiation.
The terminal derivative is the literal gradient of the physical spin partition. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorTerminalGradient (n : ℕ) (β t : ℝ) (p : Couplings n × ℝ) (x : Field n) : Field n :=
  gradient (vectorTerminalPotential n β t p) x

theorem vectorTerminalGradient_eq_magnetization (β t : ℝ) (p : Couplings n × ℝ) (x : Field n) :
    vectorTerminalGradient n β t p x = vectorMagnetization
      (Paper.parisiGridRSBScheme (Paper.diracOverlap 0 (by simp)) 0) β t p 0 x :=
  (vectorMagnetization_eq_gradient _ β t p 0 x).symm

theorem norm_vectorTerminalGradient_le (β t : ℝ) (p : Couplings n × ℝ) (x : Field n) :
    ‖vectorTerminalGradient n β t p x‖ ≤ Real.sqrt (n : ℝ) := by
  rw [vectorTerminalGradient_eq_magnetization]
  exact norm_vectorMagnetization_le_sqrt _ β t p 0 x

theorem continuous_vectorTerminalGradient (β t : ℝ) :
    Continuous (fun p : VectorParameter n => vectorTerminalGradient n β t p.1 p.2) := by
  simp_rw [vectorTerminalGradient_eq_magnetization]
  exact (contDiff_vectorMagnetization_joint _ β t 0).continuous

theorem hasDerivAt_vectorTerminalPotential_line (β t : ℝ) (p : Couplings n × ℝ)
    (x w : Field n) (r : ℝ) :
    HasDerivAt (fun a => vectorTerminalPotential n β t p (x+a • w))
      (inner ℝ (vectorTerminalGradient n β t p (x+r • w)) w) r := by
  rw [vectorTerminalGradient_eq_magnetization]
  exact hasDerivAt_vectorRecursion_field_gradient _ β t p 0 x w r

theorem norm_vectorIntegratedControlDrift_le (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    ‖vectorIntegratedDrift (fun s => vectorControlDrift c μ A s sample) r‖ ≤
      |c| *Real.sqrt (n : ℝ)*(r : ℝ) := by
  let D : ℝ≥0 := (|c| *Real.sqrt (n : ℝ)).toNNReal
  have hD : (D : ℝ)=|c| *Real.sqrt (n : ℝ) := Real.coe_toNNReal _ (by positivity)
  have hh := vectorIntegratedDrift_increment_bound
    (fun s => vectorControlDrift c μ A s sample)
    (measurable_vectorControlDrift c μ A hA).of_uncurry_right D
    (fun s => by rw [hD]; exact norm_vectorControlDrift_le c μ A hA s sample)
    (show (0 : ℝ≥0) ≤ r from bot_le)
  simpa only [vectorIntegratedDrift,Ioc_self,Measure.restrict_empty,integral_zero_measure,
    sub_zero,NNReal.coe_zero,hD] using hh

theorem norm_vectorControlledState_sub_le (c : ℝ) (μ ν : Paper.ParisiMeasure)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (sample : VectorDisorderBrownianSample n) :
    ‖vectorControlledState c ν A 1 sample-vectorControlledState c μ A 1 sample‖ ≤
      2*|c| *Real.sqrt (n : ℝ) := by
  unfold vectorControlledState
  rw [add_sub_add_left_eq_sub]
  exact (norm_sub_le _ _).trans (by
    have hμ := norm_vectorIntegratedControlDrift_le c μ A hA 1 sample
    have hν := norm_vectorIntegratedControlDrift_le c ν A hA 1 sample
    simp only [NNReal.coe_one,mul_one] at hμ hν
    linarith)

theorem norm_vectorParisiControlIntegratedCost_le (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (sample : VectorDisorderBrownianSample n) :
    ‖vectorParisiControlIntegratedCost c μ A sample‖ ≤ |c|/2*(n : ℝ) := by
  have hh := norm_setIntegral_le_of_norm_le_const
    (lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1))
    (fun r (_ : r ∈ Ioc (0 : ℝ≥0) 1) => norm_vectorParisiControlCost_le c μ A hA r sample)
  simpa only [vectorParisiControlIntegratedCost,Measure.real,nonnegativeLebesgueMeasure_Ioc,
    NNReal.coe_zero,NNReal.coe_one,sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,mul_one] using hh

theorem measurable_vectorParisiControlIntegratedCost (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A) :
    Measurable (vectorParisiControlIntegratedCost c μ A) :=
  (measurable_vectorParisiControlCost c μ A hA).stronglyMeasurable.integral_prod_left.measurable

def vectorAffineControlPayoff (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (lam : ℝ)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  let c := (1-t)*β^2
  let X := vectorControlledState c μ A 1 sample
  let Y := vectorControlledState c ν A 1 sample
  vectorTerminalPotential n β t sample.1 (X+lam • (Y-X)) -
    (vectorParisiControlIntegratedCost c μ A sample +
      lam*(vectorParisiControlIntegratedCost c ν A sample-vectorParisiControlIntegratedCost c μ A sample))

def vectorAffineControlDerivative (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (lam : ℝ)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  let c := (1-t)*β^2
  let X := vectorControlledState c μ A 1 sample
  let Y := vectorControlledState c ν A 1 sample
  inner ℝ (vectorTerminalGradient n β t sample.1 (X+lam • (Y-X))) (Y-X) -
    (vectorParisiControlIntegratedCost c ν A sample-vectorParisiControlIntegratedCost c μ A sample)

theorem hasDerivAt_vectorAffineControlPayoff (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (lam : ℝ)
    (sample : VectorDisorderBrownianSample n) :
    HasDerivAt (fun a => vectorAffineControlPayoff μ ν β t A a sample)
      (vectorAffineControlDerivative μ ν β t A lam sample) lam := by
  have hc := (((hasDerivAt_id lam).mul_const
    (vectorParisiControlIntegratedCost ((1-t)*β^2) ν A sample-
      vectorParisiControlIntegratedCost ((1-t)*β^2) μ A sample)).const_add
        (vectorParisiControlIntegratedCost ((1-t)*β^2) μ A sample))
  simp only [id_eq,one_mul] at hc
  exact (hasDerivAt_vectorTerminalPotential_line β t sample.1 _ _ lam).sub hc

theorem norm_vectorAffineControlDerivative_le (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (lam : ℝ) (sample : VectorDisorderBrownianSample n) :
    ‖vectorAffineControlDerivative μ ν β t A lam sample‖ ≤ 3*|(1-t)*β^2| *(n : ℝ) := by
  let c := (1-t)*β^2
  have hμ := norm_vectorParisiControlIntegratedCost_le c μ A hA sample
  have hν := norm_vectorParisiControlIntegratedCost_le c ν A hA sample
  have hD := norm_vectorControlledState_sub_le c μ ν A hA sample
  unfold vectorAffineControlDerivative
  dsimp only
  calc
    _ ≤ ‖inner ℝ (vectorTerminalGradient n β t sample.1 _)
        (vectorControlledState c ν A 1 sample-vectorControlledState c μ A 1 sample)‖ +
      ‖vectorParisiControlIntegratedCost c ν A sample-vectorParisiControlIntegratedCost c μ A sample‖ := norm_sub_le _ _
    _ ≤ Real.sqrt (n : ℝ)*(2*|c| *Real.sqrt (n : ℝ)) + |c| *(n : ℝ) := by
      apply add_le_add
      · exact (norm_inner_le_norm _ _).trans (mul_le_mul (norm_vectorTerminalGradient_le β t sample.1 _)
          hD (norm_nonneg _) (Real.sqrt_nonneg _))
      · exact (norm_sub_le _ _).trans (by linarith)
    _ = _ := by rw [show Real.sqrt (n : ℝ)*(2*|c| *Real.sqrt (n : ℝ)) =
        2*|c| *(Real.sqrt (n : ℝ))^2 from by ring,Real.sq_sqrt (Nat.cast_nonneg n)]; ring

theorem vectorAffineControlPayoff_eq_mix (μ ν : Paper.ParisiMeasure) (β t lam : ℝ)
    (hlam : lam ∈ Icc (0 : ℝ) 1)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (sample : VectorDisorderBrownianSample n) :
    vectorAffineControlPayoff μ ν β t A lam sample =
      vectorTerminalPotential n β t sample.1
        (vectorControlledState ((1-t)*β^2) (Paper.parisiMix μ ν lam) A 1 sample) -
      vectorParisiControlIntegratedCost ((1-t)*β^2) (Paper.parisiMix μ ν lam) A sample := by
  rw [vectorControlledState_mix _ μ ν lam hlam A hA,
    vectorParisiControlIntegratedCost_mix _ μ ν lam hlam A hA]
  dsimp only [vectorAffineControlPayoff]
  have he : vectorControlledState ((1-t)*β^2) μ A 1 sample +
      lam • (vectorControlledState ((1-t)*β^2) ν A 1 sample-
        vectorControlledState ((1-t)*β^2) μ A 1 sample) =
      (1-lam) • vectorControlledState ((1-t)*β^2) μ A 1 sample +
        lam • vectorControlledState ((1-t)*β^2) ν A 1 sample := by module
  rw [he]
  ring

end QuantitativePaper
