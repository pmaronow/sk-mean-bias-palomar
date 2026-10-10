module
public import QuantitativePaper.VectorAdditiveAdapted

@[expose] public section

/-! The constructed vector state has a genuine bounded adapted drift and an
exact all-path additive decomposition. The drift is frozen after the chosen
horizon while its Brownian noise continues. -/
noncomputable section
open FourPapersCommon Function MeasureTheory ProbabilityTheory Set StochasticCalculus
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1500000
variable {n : ℕ}

def vectorAdditiveDrift (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : Field n :=
  if r ≤ T then d.drift r sample.1 (vectorAdditiveState d σ x0 T r sample) else 0

theorem measurable_uncurry_vectorAdditiveDrift (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T : ℝ≥0) :
    Measurable (Function.uncurry (vectorAdditiveDrift d σ x0 T)) := by
  exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
    (d.measurable.comp (measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk (measurable_uncurry_vectorAdditiveState d σ x0 T))))
    measurable_const

theorem norm_vectorAdditiveDrift_le (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    ‖vectorAdditiveDrift d σ x0 T r sample‖ ≤ d.bound := by
  by_cases h : r ≤ T
  · simpa only [vectorAdditiveDrift,ite_eq_left h] using
      d.norm_le r sample.1 (vectorAdditiveState d σ x0 T r sample)
  · simp [vectorAdditiveDrift,h]

theorem integrableOn_vectorAdditiveDrift (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T a b : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    IntegrableOn (fun r => vectorAdditiveDrift d σ x0 T r sample)
      (Ioc a b) nonnegativeLebesgueMeasure :=
  integrableOn_bounded_vector_drift _
    (measurable_uncurry_vectorAdditiveDrift d σ x0 T).of_uncurry_right
    d.bound (fun r => norm_vectorAdditiveDrift_le d σ x0 T r sample) a b

theorem vectorIntegral_Ioc_eq_interval (f : ℝ≥0 → Field n) (r : ℝ≥0) :
    (∫ s in Ioc (0 : ℝ≥0) r,f s ∂nonnegativeLebesgueMeasure) =
      ∫ s in (0 : ℝ)..(r : ℝ),f s.toNNReal := by
  have hp : MeasurePreserving ((↑) : ℝ≥0 → ℝ)
      (nonnegativeLebesgueMeasure.restrict (Ioc 0 r))
      (volume.restrict (Ioc (0 : ℝ) (r : ℝ))) :=
    ⟨NNReal.continuous_coe.measurable,map_nonnegativeLebesgueMeasure_restrict_Ioc r⟩
  have he := hp.integral_comp measurableEmbedding_nnrealCoe_iterated
    (fun s : ℝ => f s.toNNReal)
  simpa only [Real.toNNReal_coe,intervalIntegral.integral_of_le r.coe_nonneg] using he

private theorem correction_compProj_min (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    (vectorAdditiveCorrection d σ x0 T sample).compProj r =
      (vectorAdditiveCorrection d σ x0 T sample).compProj (min r T) := by
  by_cases h : r ≤ T
  · rw [min_eq_left (show (r : ℝ) ≤ T from h)]
  · rw [min_eq_right (show (T : ℝ) ≤ r from le_of_not_ge h),ODE.FunSpace.compProj_apply,
      ODE.FunSpace.compProj_apply,projIcc_of_right_le _ (show (T : ℝ) ≤ r from le_of_not_ge h),
      projIcc_right]

theorem vectorIntegratedAdditiveDrift_eq_min (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    vectorIntegratedDrift (fun s => vectorAdditiveDrift d σ x0 T s sample) r =
      ∫ s in Ioc (0 : ℝ≥0) (min r T),
        d.drift s sample.1 (vectorAdditiveState d σ x0 T s sample)
        ∂nonnegativeLebesgueMeasure := by
  change (∫ s in Ioc (0 : ℝ≥0) r,(Iic T).indicator
    (fun s => d.drift s sample.1 (vectorAdditiveState d σ x0 T s sample)) s
    ∂nonnegativeLebesgueMeasure) = _
  rw [setIntegral_indicator measurableSet_Iic]
  have hset : Ioc (0 : ℝ≥0) r ∩ Iic T = Ioc 0 (min r T) := by
    ext s
    simp only [mem_inter_iff,mem_Ioc,mem_Iic,le_min_iff]
    tauto
  rw [hset]

/-- Exact drift/Brownian decomposition for every sample and every nonnegative time. -/
theorem vectorAdditiveState_decomposition (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    vectorAdditiveState d σ x0 T r sample = x0 +
      vectorIntegratedDrift (fun s => vectorAdditiveDrift d σ x0 T s sample) r +
      σ • disorderVectorBrownian r sample := by
  rw [vectorIntegratedAdditiveDrift_eq_min,vectorIntegral_Ioc_eq_interval]
  have he := vectorAdditiveState_equation d σ x0 T (min r T) (min_le_right _ _) sample
  unfold vectorAdditiveState at he ⊢
  rw [correction_compProj_min d σ x0 T r sample]
  have hc : (vectorAdditiveCorrection d σ x0 T sample).compProj (min r T) = x0 +
      ∫ s in (0 : ℝ)..(min r T : ℝ≥0),d.drift s.toNNReal sample.1
        ((vectorAdditiveCorrection d σ x0 T sample).compProj s.toNNReal +
          σ • disorderVectorBrownian s.toNNReal sample) := by
    apply add_right_cancel (b := σ • disorderVectorBrownian (min r T) sample)
    calc
      _ = x0 + σ • disorderVectorBrownian (min r T) sample + _ := he
      _ = _ := by abel
  rw [hc]

end QuantitativePaper
