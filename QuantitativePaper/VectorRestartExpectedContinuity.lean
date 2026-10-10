module
public import QuantitativePaper.VectorRestartExponentialEnvelope

@[expose] public section

/-! Actual expected exponential-growth tests are continuous at both ends
of a restart interval. The dominating function is the constructed Wiener
path envelope, uniformly over every time in the interval. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem continuousOn_vectorRestart_expected_exp_test
    (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (a b : ℝ) (ha : 0≤a) (hb : b≤1)
    (F : ℝ×Field n→ℝ) (hF : ContinuousOn F (Icc a b×ˢuniv))
    (C R : ℝ) (hC : 0≤C) (hR : 0≤R)
    (hbound : ∀r∈Icc a b,∀y,|F (r,y)|≤C*Real.exp (R*‖y‖)) :
    ContinuousOn (fun r=>∫sample : VectorDisorderBrownianSample n,
      F (r,vectorRestartState μ β t ht q p x r.toNNReal sample)
      ∂vectorDisorderBrownianMeasure n) (Icc a b) := by
  let M : VectorDisorderBrownianSample n→ℝ:=fun sample=>
    C*vectorRestartExponentialEnvelope β t R x sample
  have hi : Integrable M (vectorDisorderBrownianMeasure n):=
    (integrable_vectorRestartExponentialEnvelope β t R x).const_mul C
  have hs (r : ℝ) (hr : r∈Icc a b) : Continuous (fun y : Field n=>F (r,y)):=by
    rw [←continuousOn_univ]
    exact hF.comp (f:=fun y : Field n=>(r,y)) (g:=F)
      (continuous_const.prodMk continuous_id).continuousOn (fun _ _=>⟨hr,mem_univ _⟩)
  apply continuousOn_of_dominated (bound:=M)
  · intro r hr
    have hX : Measurable (vectorRestartState μ β t ht q p x r.toNNReal):=
      (measurable_uncurry_vectorRestartState μ β t ht q p x).of_uncurry_left
    exact ((hs r hr).measurable.comp hX).aestronglyMeasurable
  · intro r hr
    exact .of_forall fun sample=>by
      have hr1 : r.toNNReal≤(1 : ℝ≥0):=by
        simpa only [Real.toNNReal_one] using Real.toNNReal_le_toNNReal (hr.2.trans hb)
      have he : Real.exp (R*‖vectorRestartState μ β t ht q p x r.toNNReal sample‖)≤
          vectorRestartExponentialEnvelope β t R x sample := by
        apply le_trans _ (exp_vectorRestartState_and_disorder_le_envelope
          μ β t R ht q p x r.toNNReal hr1 sample)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg sample.1]) hR
      rw [Real.norm_eq_abs]
      exact (hbound r hr _).trans (mul_le_mul_of_nonneg_left he hC)
  · exact hi
  · exact .of_forall fun sample=>by
      have hp : Continuous (fun r : ℝ=>(r,vectorRestartState μ β t ht q p x r.toNNReal sample)):=
        continuous_id.prodMk ((continuous_vectorRestartState μ β t ht q p x sample).comp
          continuous_real_toNNReal)
      exact hF.comp (f:=fun r : ℝ=>(r,vectorRestartState μ β t ht q p x r.toNNReal sample))
        (g:=F) hp.continuousOn (fun r hr=>⟨hr,mem_univ _⟩)

end QuantitativePaper
