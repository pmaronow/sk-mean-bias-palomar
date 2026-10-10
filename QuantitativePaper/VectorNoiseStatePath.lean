module
public import QuantitativePaper.VectorAdditiveUniqueness
public import QuantitativePaper.VectorBrownianSplicing

@[expose] public section

/-! A jointly measurable actual Picard solution driven by a supplied
continuous Wiener path, with arbitrary initial disorder and field. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

abbrev VectorNoiseInitialData (n : ℕ) := ((Couplings n×ℝ)×Field n)×VectorWienerPath n

def vectorContinuousNoise (V : VectorWienerPath n) (r : ℝ) : Field n :=
  WithLp.toLp 2 (fun i=>V i (projIcc (0:ℝ) 1 zero_le_one r)-V i 0)

theorem continuous_vectorContinuousNoise :
    Continuous (fun z : ℝ×VectorWienerPath n=>vectorContinuousNoise z.2 z.1) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n=>ℝ)).comp
  apply continuous_pi
  intro i
  exact ((continuous_eval.comp (((continuous_apply i).comp continuous_snd).prodMk
    ((continuous_projIcc (h:=zero_le_one)).comp continuous_fst))).sub
      ((continuous_eval_const (0:Paper.Overlap)).comp ((continuous_apply i).comp continuous_snd)))

@[simp] theorem vectorContinuousNoise_zero (V : VectorWienerPath n) :
    vectorContinuousNoise V 0=0 := by
  ext i
  simp [vectorContinuousNoise,projIcc_of_mem]

theorem vectorContinuousNoise_canonical (sample : VectorDisorderBrownianSample n)
    (r : ℝ≥0) (hr : r≤1) :
    vectorContinuousNoise (vectorCanonicalBrownianPath sample.2) r=disorderVectorBrownian r sample := by
  ext i
  have he:=projIcc_of_mem zero_le_one (show (r:ℝ)∈Icc (0:ℝ) 1 from ⟨r.coe_nonneg,hr⟩)
  simp [vectorContinuousNoise,PiLp.toLp_apply,he,vectorCanonicalBrownianPath,
    Paper.canonicalBrownianPath,disorderVectorBrownian,vectorBrownian_apply]

def vectorContinuousNoiseDrift (d : VectorAdditiveDriftData n) (σ : ℝ)
    (z : VectorNoiseInitialData n) (r : ℝ) (y : Field n) : Field n :=
  d.drift r.toNNReal z.1.1 (z.1.2+y+σ • vectorContinuousNoise z.2 r)

theorem bounded_vectorContinuousNoiseDrift (d : VectorAdditiveDriftData n) (σ : ℝ)
    (z : VectorNoiseInitialData n) :
    IsBoundedVectorDrift (vectorContinuousNoiseDrift d σ z) d.bound d.spatialLip where
  measurable := d.measurable.comp
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      (measurable_const.prodMk ((measurable_const.add measurable_snd).add
        (((continuous_vectorContinuousNoise.comp (continuous_fst.prodMk continuous_const)).measurable).const_smul σ))))
  norm_le := fun _ _=>d.norm_le _ _ _
  lipschitz r := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [vectorContinuousNoiseDrift,dist_add_right,dist_add_left] using
      (d.lipschitz r.toNNReal z.1.1).dist_le_mul (z.1.2+x+σ • vectorContinuousNoise z.2 r)
        (z.1.2+y+σ • vectorContinuousNoise z.2 r)

theorem measurable_vectorContinuousNoiseDrift (d : VectorAdditiveDriftData n) (σ : ℝ) :
    Measurable (fun z : (ℝ×Field n)×VectorNoiseInitialData n=>
      vectorContinuousNoiseDrift d σ z.2 z.1.1 z.1.2) := by
  exact d.measurable.comp
    ((continuous_real_toNNReal.measurable.comp measurable_fst.fst).prodMk
      (measurable_snd.fst.fst.prodMk ((measurable_snd.fst.snd.add measurable_fst.snd).add
        ((continuous_vectorContinuousNoise.measurable.comp
          (measurable_fst.fst.prodMk measurable_snd.snd)).const_smul σ))))

def vectorNoiseStatePath (d : VectorAdditiveDriftData n) (σ : ℝ)
    (T : ℝ≥0) (z : VectorNoiseInitialData n) (r : ℝ) : Field n :=
  z.1.2+(VectorIntegralPicard.solution (h:=(0:Field n)) T.coe_nonneg
    (bounded_vectorContinuousNoiseDrift d σ z)).compProj r+σ • vectorContinuousNoise z.2 r

theorem continuous_vectorNoiseStatePath (d : VectorAdditiveDriftData n) (σ : ℝ)
    (T : ℝ≥0) (z : VectorNoiseInitialData n) : Continuous (vectorNoiseStatePath d σ T z) :=
  ((ODE.FunSpace.continuous_compProj _).const_add _).add
    ((continuous_vectorContinuousNoise.comp (continuous_id.prodMk continuous_const)).const_smul σ)

theorem measurable_uncurry_vectorNoiseStatePath (d : VectorAdditiveDriftData n) (σ : ℝ)
    (T : ℝ≥0) :
    Measurable (fun z : ℝ×VectorNoiseInitialData n=>vectorNoiseStatePath d σ T z.2 z.1) := by
  have hC:=VectorIntegralPicard.measurable_uncurry_solution_compProj T.coe_nonneg (0:Field n)
    (vectorContinuousNoiseDrift d σ) (bounded_vectorContinuousNoiseDrift d σ)
    (measurable_vectorContinuousNoiseDrift d σ)
  exact (measurable_snd.fst.snd.add hC).add
    ((continuous_vectorContinuousNoise.measurable.comp (measurable_fst.prodMk measurable_snd.snd)).const_smul σ)

theorem vectorNoiseStatePath_equation (d : VectorAdditiveDriftData n) (σ : ℝ)
    (T : ℝ≥0) (z : VectorNoiseInitialData n) (r : ℝ) (hr : r∈Icc (0:ℝ) T) :
    vectorNoiseStatePath d σ T z r=z.1.2+σ • vectorContinuousNoise z.2 r+
      ∫s in 0..r,d.drift s.toNNReal z.1.1 (vectorNoiseStatePath d σ T z s) := by
  have he:=VectorIntegralPicard.solution_compProj_equation (x0:=(0:Field n)) T.coe_nonneg
    (bounded_vectorContinuousNoiseDrift d σ z) hr
  unfold vectorNoiseStatePath
  rw [he,zero_add]
  have hi : (∫s in 0..r,vectorContinuousNoiseDrift d σ z s
      ((VectorIntegralPicard.solution (h:=(0:Field n)) T.coe_nonneg
        (bounded_vectorContinuousNoiseDrift d σ z)).compProj s))=
      ∫s in 0..r,d.drift s.toNNReal z.1.1
        (z.1.2+(VectorIntegralPicard.solution (h:=(0:Field n)) T.coe_nonneg
          (bounded_vectorContinuousNoiseDrift d σ z)).compProj s+σ • vectorContinuousNoise z.2 s) := rfl
  rw [hi]
  abel

theorem vectorNoiseStatePath_canonical (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x : Field n) (T : ℝ≥0) (hT : T≤1) (sample : VectorDisorderBrownianSample n)
    (r : ℝ≥0) (hr : r≤T) :
    vectorNoiseStatePath d σ T ((sample.1,x),vectorCanonicalBrownianPath sample.2) r=
      vectorAdditiveState d σ x T r sample := by
  apply vectorAdditiveState_unique d σ x T sample
    (fun s=>vectorNoiseStatePath d σ T ((sample.1,x),vectorCanonicalBrownianPath sample.2) s)
    ((continuous_vectorNoiseStatePath d σ T _).comp NNReal.continuous_coe) ?_ r hr
  intro u hu
  rw [vectorIntegral_Ioc_eq_interval]
  have he:=vectorNoiseStatePath_equation d σ T ((sample.1,x),vectorCanonicalBrownianPath sample.2)
    u ⟨u.coe_nonneg,hu⟩
  rw [vectorContinuousNoise_canonical sample u (hu.trans hT)] at he
  change _=x+σ • disorderVectorBrownian u sample+_ at he
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le u.coe_nonneg] at hs
  dsimp only
  rw [Real.coe_toNNReal s hs.1]

end QuantitativePaper
