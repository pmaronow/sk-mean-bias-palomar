module
public import QuantitativePaper.VectorDyadicStateConvergence
public import QuantitativePaper.VectorDyadicTiltConvergence
public import QuantitativePaper.VectorFiniteSpinPathLaw

@[expose] public section

/-! Actual arbitrary-profile diffusion and terminal Gibbs-spin measure,
with genuine probability normalization and continuous terminal responses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def vectorMeasureJointState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : VectorState n :=
  (sample.1,vectorMeasureState μ β t ht r sample)

theorem measurable_vectorMeasureJointState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (r : ℝ≥0) : Measurable (vectorMeasureJointState (n:=n) μ β t ht r) :=
  measurable_fst.prodMk (((stronglyAdapted_vectorMeasureState μ β t ht r).measurable).mono
    ((vectorBrownianFiltration n).le r) le_rfl)

theorem adapted_vectorMeasureJointState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (r : ℝ≥0) : Measurable[vectorBrownianFiltration n r]
      (vectorMeasureJointState (n:=n) μ β t ht r) :=
  (stronglyMeasurable_initialVectorDisorder n r).measurable.prodMk
    (stronglyAdapted_vectorMeasureState μ β t ht r).measurable

def vectorMeasureSpinPathLaw (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) :
    Measure (VectorDisorderBrownianSample n×Configuration n) :=
  (vectorMeasureDisorderTilt μ β t a) ⊗ₘ
    ((terminalSpinKernel (fun p : VectorState n=>vectorTerminalExponent n β t p.1 p.2)
      (measurable_vectorTerminalExponent_state n β t)).comap
        (vectorMeasureJointState μ β t ht 1) (measurable_vectorMeasureJointState μ β t ht 1))

theorem vectorMeasureSpinPathLaw_probability (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) :
    IsProbabilityMeasure (vectorMeasureSpinPathLaw (n:=n) μ β t a ht) := by
  haveI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  unfold vectorMeasureSpinPathLaw
  infer_instance

theorem continuous_vectorTerminalMean_joint (β t : ℝ) (d : Configuration n→ℝ) :
    Continuous (fun p : VectorState n=>terminalMean (vectorTerminalExponent n β t p.1 p.2) d) := by
  have hE (σ : Configuration n) : Continuous (fun p : VectorState n=>
      vectorTerminalExponent n β t p.1 p.2 σ) := by
    have he : (fun p : VectorState n=>vectorTerminalExponent n β t p.1 p.2 σ)=
        vectorTerminalLinear n β t σ := by
      funext p
      exact (vectorTerminalLinear_apply n β t σ p).symm
    rw [he]
    exact (vectorTerminalLinear n β t σ).continuous
  unfold terminalMean
  apply continuous_finset_sum
  intro σ _
  apply Continuous.mul_const
  unfold terminalWeight
  exact (Real.continuous_exp.comp (hE σ)).div
    (continuous_finset_sum Finset.univ (fun τ _=>Real.continuous_exp.comp (hE τ)))
    (fun p=>(terminalPartition_pos (vectorTerminalExponent n β t p.1 p.2)).ne')

end QuantitativePaper
