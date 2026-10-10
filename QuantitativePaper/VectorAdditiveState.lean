module
public import FourPapersCommon.VectorPicardCausality
public import QuantitativePaper.VectorBrownianMoments
public import QuantitativePaper.VectorDriftBounds

@[expose] public section

/-! Actual additive-noise vector state. The only data assumptions are joint
measurability, a uniform drift bound, and a uniform spatial Lipschitz bound.
The continuous solution is constructed by the Banach-valued integral Picard
fixed point for every Wiener sample. -/
noncomputable section
open FourPapersCommon Function MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000

structure VectorAdditiveDriftData (n : ℕ) where
  drift : ℝ≥0 → (Couplings n × ℝ) → Field n → Field n
  bound : ℝ≥0
  spatialLip : ℝ≥0
  measurable : Measurable (fun p : ℝ≥0 × ((Couplings n × ℝ) × Field n) =>
    drift p.1 p.2.1 p.2.2)
  norm_le : ∀ r p x,‖drift r p x‖ ≤ bound
  lipschitz : ∀ r p,LipschitzWith spatialLip (drift r p)

variable {n : ℕ}

def vectorAdditiveNoiseReal (σ : ℝ) (r : ℝ)
    (sample : VectorDisorderBrownianSample n) : Field n :=
  σ • disorderVectorBrownian r.toNNReal sample

theorem continuous_vectorAdditiveNoiseReal (σ : ℝ)
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r => vectorAdditiveNoiseReal σ r sample) :=
  ((continuous_disorderVectorBrownian sample).comp continuous_real_toNNReal).const_smul σ

theorem measurable_uncurry_vectorAdditiveNoiseReal (σ : ℝ) :
    Measurable (Function.uncurry (vectorAdditiveNoiseReal (n := n) σ)) := by
  exact ((measurable_uncurry_disorderVectorBrownian n).comp
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)).const_smul σ

def vectorNoiseCorrectionDrift (d : VectorAdditiveDriftData n)
    (W : ℝ → VectorDisorderBrownianSample n → Field n)
    (sample : VectorDisorderBrownianSample n) (r : ℝ) (y : Field n) : Field n :=
  d.drift r.toNNReal sample.1 (y + W r sample)

theorem isBounded_vectorNoiseCorrectionDrift (d : VectorAdditiveDriftData n)
    (W : ℝ → VectorDisorderBrownianSample n → Field n)
    (hW : ∀ sample,Continuous (fun r => W r sample)) (sample : VectorDisorderBrownianSample n) :
    IsBoundedVectorDrift (vectorNoiseCorrectionDrift d W sample) d.bound d.spatialLip where
  measurable := by
    exact d.measurable.comp
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
        (measurable_const.prodMk (measurable_snd.add ((hW sample).measurable.comp measurable_fst))))
  norm_le := fun r y => d.norm_le _ _ _
  lipschitz r := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [vectorNoiseCorrectionDrift,dist_add_right] using
      (d.lipschitz r.toNNReal sample.1).dist_le_mul (y + W r sample) (z + W r sample)

theorem measurable_vectorNoiseCorrectionDrift (d : VectorAdditiveDriftData n)
    (W : ℝ → VectorDisorderBrownianSample n → Field n)
    (hW : Measurable (Function.uncurry W)) :
    Measurable (fun p : (ℝ × Field n) × VectorDisorderBrownianSample n =>
      vectorNoiseCorrectionDrift d W p.2 p.1.1 p.1.2) := by
  exact d.measurable.comp
    ((continuous_real_toNNReal.measurable.comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_fst).add
          (hW.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))))

def vectorAdditiveCorrection (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    VectorIntegralPicard.Curve T.coe_nonneg x0 d.bound :=
  VectorIntegralPicard.solution T.coe_nonneg
    (isBounded_vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ)
      (continuous_vectorAdditiveNoiseReal σ) sample)

def vectorAdditiveState (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : Field n :=
  (vectorAdditiveCorrection d σ x0 T sample).compProj r + σ • disorderVectorBrownian r sample

theorem continuous_vectorAdditiveState (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r => vectorAdditiveState d σ x0 T r sample) :=
  ((ODE.FunSpace.continuous_compProj _).comp NNReal.continuous_coe).add
    ((continuous_disorderVectorBrownian sample).const_smul σ)

theorem measurable_uncurry_vectorAdditiveState (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T : ℝ≥0) :
    Measurable (Function.uncurry (vectorAdditiveState d σ x0 T)) := by
  have hc := VectorIntegralPicard.measurable_uncurry_solution_compProj
    T.coe_nonneg x0 (vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ))
    (isBounded_vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ)
      (continuous_vectorAdditiveNoiseReal σ))
    (measurable_vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ)
      (measurable_uncurry_vectorAdditiveNoiseReal σ))
  exact (hc.comp ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)).add
    ((measurable_uncurry_disorderVectorBrownian n).const_smul σ)

theorem measurable_vectorAdditiveState (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T r : ℝ≥0) :
    Measurable (vectorAdditiveState d σ x0 T r) :=
  Measurable.of_uncurry_left (f := vectorAdditiveState d σ x0 T)
    (x := r) (measurable_uncurry_vectorAdditiveState d σ x0 T)

@[simp] theorem vectorAdditiveState_zero (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    vectorAdditiveState d σ x0 T 0 sample = x0 := by
  have he := VectorIntegralPicard.solution_compProj_equation T.coe_nonneg
    (isBounded_vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ)
      (continuous_vectorAdditiveNoiseReal σ) sample) (x0 := x0) (r := 0)
      ⟨le_rfl,T.coe_nonneg⟩
  simpa [vectorAdditiveState,vectorAdditiveCorrection,disorderVectorBrownian] using he

/-- The constructed physical state satisfies the additive-noise integral equation on every path. -/
theorem vectorAdditiveState_equation (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x0 : Field n) (T r : ℝ≥0) (hr : r ≤ T) (sample : VectorDisorderBrownianSample n) :
    vectorAdditiveState d σ x0 T r sample = x0 + σ • disorderVectorBrownian r sample +
      ∫ s in (0 : ℝ)..(r : ℝ),
        d.drift s.toNNReal sample.1 (vectorAdditiveState d σ x0 T s.toNNReal sample) := by
  have he := VectorIntegralPicard.solution_compProj_equation T.coe_nonneg
    (isBounded_vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ)
      (continuous_vectorAdditiveNoiseReal σ) sample) (x0 := x0)
      ⟨r.coe_nonneg,show (r : ℝ) ≤ T from hr⟩
  change (vectorAdditiveCorrection d σ x0 T sample).compProj r = x0 +
    ∫ s in (0 : ℝ)..(r : ℝ),vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ) sample s
      ((vectorAdditiveCorrection d σ x0 T sample).compProj s) at he
  unfold vectorAdditiveState
  rw [he]
  have hint : (∫ s in (0 : ℝ)..(r : ℝ),vectorNoiseCorrectionDrift d
      (vectorAdditiveNoiseReal σ) sample s
        ((vectorAdditiveCorrection d σ x0 T sample).compProj s)) =
      ∫ s in (0 : ℝ)..(r : ℝ),d.drift s.toNNReal sample.1
        ((vectorAdditiveCorrection d σ x0 T sample).compProj s.toNNReal +
          σ • disorderVectorBrownian s.toNNReal sample) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le r.coe_nonneg] at hs
    simp only [vectorNoiseCorrectionDrift,vectorAdditiveNoiseReal,
      Real.coe_toNNReal s hs.1]
  rw [hint]
  abel

end QuantitativePaper
