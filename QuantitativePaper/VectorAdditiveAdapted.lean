module
public import QuantitativePaper.VectorAdditiveState

@[expose] public section

/-! Adaptation follows from causality of the actual Picard construction.
Freezing a Wiener path at the observation time gives a solution measurable in
the past filtration; uniqueness identifies its current value with the
unfrozen solution. Initial SK disorder belongs to the same enlarged past. -/
noncomputable section
open FourPapersCommon Function MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1500000
variable {n : ℕ}

def pastVectorAdditiveNoise (σ : ℝ) (a : ℝ≥0) (r : ℝ)
    (sample : VectorDisorderBrownianSample n) : Field n :=
  σ • disorderVectorBrownian (min r.toNNReal a) sample

theorem continuous_pastVectorAdditiveNoise (σ : ℝ) (a : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r => pastVectorAdditiveNoise σ a r sample) :=
  ((continuous_disorderVectorBrownian sample).comp
    (continuous_real_toNNReal.min continuous_const)).const_smul σ

theorem measurable_pastVectorAdditiveNoise (σ : ℝ) (a : ℝ≥0) :
    @Measurable (ℝ × VectorDisorderBrownianSample n) (Field n)
      ((inferInstance : MeasurableSpace ℝ).prod (vectorBrownianFiltration n a)) inferInstance
      (Function.uncurry (pastVectorAdditiveNoise σ a)) := by
  letI : MeasurableSpace (VectorDisorderBrownianSample n) := vectorBrownianFiltration n a
  apply measurable_uncurry_of_continuous_of_measurable
    (continuous_pastVectorAdditiveNoise σ a)
  intro r
  exact (((stronglyAdapted_disorderVectorBrownian n (min r.toNNReal a)).mono
    ((vectorBrownianFiltration n).mono (min_le_right _ _))).measurable).const_smul σ

private theorem compProj_eq_min {x0 : Field n} {L : ℝ≥0} (T r : ℝ≥0)
    (α : VectorIntegralPicard.Curve T.coe_nonneg x0 L) :
    α.compProj r = α.compProj (min r T) := by
  by_cases h : r ≤ T
  · rw [min_eq_left (show (r : ℝ) ≤ T from h)]
  · rw [min_eq_right (show (T : ℝ) ≤ r from le_of_not_ge h),ODE.FunSpace.compProj_apply,
      ODE.FunSpace.compProj_apply,projIcc_of_right_le _ (show (T : ℝ) ≤ r from le_of_not_ge h),
      projIcc_right]

theorem vectorAdditiveCorrection_eq_past (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    (vectorAdditiveCorrection d σ x0 T sample).compProj r =
      (VectorIntegralPicard.solution (h := x0) T.coe_nonneg
        (isBounded_vectorNoiseCorrectionDrift d (pastVectorAdditiveNoise σ r)
          (continuous_pastVectorAdditiveNoise σ r) sample)).compProj r := by
  let hf := isBounded_vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ)
    (continuous_vectorAdditiveNoiseReal σ) sample
  let hg := isBounded_vectorNoiseCorrectionDrift d (pastVectorAdditiveNoise σ r)
    (continuous_pastVectorAdditiveNoise σ r) sample
  have hfg : ∀ s ∈ Icc (0 : ℝ) (min r T : ℝ≥0),∀ y,
      vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ) sample s y =
      vectorNoiseCorrectionDrift d (pastVectorAdditiveNoise σ r) sample s y := by
    intro s hs y
    have hsr : s.toNNReal ≤ r := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hs.1]
      exact hs.2.trans (show (min r T : ℝ≥0) ≤ r from min_le_left _ _)
    simp only [vectorNoiseCorrectionDrift,vectorAdditiveNoiseReal,pastVectorAdditiveNoise,
      min_eq_left hsr]
  have hc := VectorIntegralPicard.solution_causal (x0 := x0) T.coe_nonneg (min r T).coe_nonneg
    (show (min r T : ℝ) ≤ T from min_le_right _ _) hf hg hfg
    (min r T) ⟨(min r T).coe_nonneg,le_rfl⟩
  change (VectorIntegralPicard.solution (h := x0) T.coe_nonneg hf).compProj r =
    (VectorIntegralPicard.solution (h := x0) T.coe_nonneg hg).compProj r
  rw [compProj_eq_min T r,compProj_eq_min T r]
  exact hc

/-- The actual vector state is adapted to Wiener paths and independent initial disorder. -/
theorem stronglyAdapted_vectorAdditiveState (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T : ℝ≥0) :
    StronglyAdapted (vectorBrownianFiltration n) (vectorAdditiveState d σ x0 T) := by
  intro r
  letI : MeasurableSpace (VectorDisorderBrownianSample n) := vectorBrownianFiltration n r
  have hD : Measurable (Prod.fst : VectorDisorderBrownianSample n → Couplings n × ℝ) :=
    (stronglyMeasurable_initialVectorDisorder n r).measurable
  have hW := measurable_pastVectorAdditiveNoise (n := n) σ r
  have hf : Measurable (fun p : (ℝ × Field n) × VectorDisorderBrownianSample n =>
      vectorNoiseCorrectionDrift d (pastVectorAdditiveNoise σ r) p.2 p.1.1 p.1.2) := by
    exact d.measurable.comp
      ((continuous_real_toNNReal.measurable.comp (measurable_fst.comp measurable_fst)).prodMk
        ((hD.comp measurable_snd).prodMk
          ((measurable_snd.comp measurable_fst).add
            (hW.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))))
  have hm := VectorIntegralPicard.measurable_solution_compProj T.coe_nonneg x0
    (vectorNoiseCorrectionDrift d (pastVectorAdditiveNoise σ r))
    (isBounded_vectorNoiseCorrectionDrift d (pastVectorAdditiveNoise σ r)
      (continuous_pastVectorAdditiveNoise σ r)) hf (r : ℝ)
  have he : (fun sample => (vectorAdditiveCorrection d σ x0 T sample).compProj r) =
      (fun sample => (VectorIntegralPicard.solution (h := x0) T.coe_nonneg
        (isBounded_vectorNoiseCorrectionDrift d (pastVectorAdditiveNoise σ r)
          (continuous_pastVectorAdditiveNoise σ r) sample)).compProj r) :=
    funext (vectorAdditiveCorrection_eq_past d σ x0 T r)
  have hcor : Measurable (fun sample => (vectorAdditiveCorrection d σ x0 T sample).compProj r) := by
    rw [he]
    exact hm
  change StronglyMeasurable (fun sample =>
    (vectorAdditiveCorrection d σ x0 T sample).compProj r+σ • disorderVectorBrownian r sample)
  exact hcor.stronglyMeasurable.add ((stronglyAdapted_disorderVectorBrownian n r).const_smul σ)

end QuantitativePaper
