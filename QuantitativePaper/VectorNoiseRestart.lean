module
public import QuantitativePaper.VectorNoiseStatePathUniqueness
public import QuantitativePaper.VectorRestartState

@[expose] public section

/-! Actual pathwise restart, using the complete future continuous Wiener path. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorTimeShiftDriftData (d : VectorAdditiveDriftData n) (q : ℝ≥0) :
    VectorAdditiveDriftData n where
  drift r p x := d.drift (q+r) p x
  bound := d.bound
  spatialLip := d.spatialLip
  measurable := d.measurable.comp
    ((measurable_const.add measurable_fst).prodMk measurable_snd)
  norm_le r p x := d.norm_le _ p x
  lipschitz r p := d.lipschitz _ p

def vectorNoiseRestartStatePath (d : VectorAdditiveDriftData n) (σ : ℝ)
    (q : Paper.Overlap) (z : VectorNoiseInitialData n) (r : ℝ) : Field n :=
  vectorNoiseStatePath (vectorTimeShiftDriftData d (q:ℝ).toNNReal) σ
    (vectorRestartHorizon q) z r

theorem measurable_uncurry_vectorNoiseRestartStatePath (d : VectorAdditiveDriftData n)
    (σ : ℝ) (q : Paper.Overlap) :
    Measurable (fun z : ℝ×VectorNoiseInitialData n=>vectorNoiseRestartStatePath d σ q z.2 z.1) :=
  measurable_uncurry_vectorNoiseStatePath _ _ _

theorem vectorContinuousNoise_future (q : ℝ≥0) (sample : VectorDisorderBrownianSample n)
    (r : ℝ≥0) (hr : r≤1) :
    vectorContinuousNoise (vectorFutureBrownianPath q sample) r=
      disorderVectorBrownian (q+r) sample-disorderVectorBrownian q sample := by
  ext i
  have he:=projIcc_of_mem zero_le_one (show (r:ℝ)∈Icc (0:ℝ) 1 from ⟨r.coe_nonneg,hr⟩)
  simp [vectorContinuousNoise,PiLp.toLp_apply,he,vectorFutureBrownianPath,
    canonicalFutureBrownianPath,disorderVectorBrownian,vectorBrownian_apply]

theorem vectorAdditiveState_restart (d : VectorAdditiveDriftData n) (σ : ℝ)
    (x : Field n) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n)
    (r : ℝ≥0) (hr : r≤vectorRestartHorizon q) :
    vectorAdditiveState d σ x 1 ((q:ℝ).toNNReal+r) sample=
      vectorNoiseRestartStatePath d σ q
        ((sample.1,vectorAdditiveState d σ x 1 (q:ℝ).toNNReal sample),
          vectorFutureBrownianPath (q:ℝ).toNNReal sample) r := by
  let a : ℝ≥0 := (q:ℝ).toNNReal
  have ha : (a:ℝ)=(q:ℝ) := Real.coe_toNNReal _ q.property.1
  have hH : ((vectorRestartHorizon q:ℝ≥0):ℝ)=1-(q:ℝ) :=
    Real.coe_toNNReal _ (sub_nonneg.mpr q.property.2)
  let X : ℝ→Field n := fun s=>vectorAdditiveState d σ x 1 (a+s.toNNReal) sample
  have hX : Continuous X := (continuous_vectorAdditiveState d σ x 1 sample).comp
    (continuous_const.add continuous_real_toNNReal)
  let f : ℝ→Field n := fun s=>d.drift s.toNNReal sample.1
    (vectorAdditiveState d σ x 1 s.toNNReal sample)
  have hfi (u v : ℝ) : IntervalIntegrable f volume u v := by
    apply (intervalIntegrable_const (c:=(d.bound:ℝ))).mono_fun'
      (d.measurable.comp ((continuous_real_toNNReal.measurable).prodMk
        (measurable_const.prodMk ((continuous_vectorAdditiveState d σ x 1 sample).measurable.comp
          continuous_real_toNNReal.measurable)))).aestronglyMeasurable
    exact .of_forall (fun s=>d.norm_le _ _ _)
  let z : VectorNoiseInitialData n :=
    ((sample.1,vectorAdditiveState d σ x 1 a sample),vectorFutureBrownianPath a sample)
  have he : ∀s∈Icc (0:ℝ) (vectorRestartHorizon q),X s=z.1.2+
      σ • vectorContinuousNoise z.2 s+
      ∫u in 0..s,(vectorTimeShiftDriftData d a).drift u.toNNReal z.1.1 (X u) := by
    intro s hs
    have hsH : s≤1-(q:ℝ) := by simpa only [hH] using hs.2
    have hs1 : s≤1 := by linarith [q.property.1]
    have hsa : a+s.toNNReal≤1 := by
      apply NNReal.coe_le_coe.mp
      simp only [NNReal.coe_add,NNReal.coe_one,Real.coe_toNNReal s hs.1,ha]
      linarith
    have hea:=vectorAdditiveState_equation d σ x 1 a (by
      apply NNReal.coe_le_coe.mp;simpa only [ha,NNReal.coe_one] using q.property.2) sample
    have hes:=vectorAdditiveState_equation d σ x 1 (a+s.toNNReal) hsa sample
    have hi : (∫u in 0..s,(vectorTimeShiftDriftData d a).drift u.toNNReal z.1.1 (X u))=
        ∫u in (a:ℝ)..((a:ℝ)+s),f u := by
      calc
        _=∫u in 0..s,f ((a:ℝ)+u) := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [uIcc_of_le hs.1] at hu
          dsimp only [f,X,z,vectorTimeShiftDriftData]
          rw [Real.toNNReal_add a.coe_nonneg hu.1]
          rw [Real.toNNReal_coe]
        _=_ := by simpa only [add_zero] using
          intervalIntegral.integral_comp_add_left (a:=(0:ℝ)) (b:=s) f (a:ℝ)
    have hn:=vectorContinuousNoise_future a sample s.toNNReal (by
      apply NNReal.coe_le_coe.mp;simpa only [Real.coe_toNNReal s hs.1,NNReal.coe_one] using hs1)
    rw [Real.coe_toNNReal s hs.1] at hn
    have hadj:=intervalIntegral.integral_add_adjacent_intervals (hfi 0 a) (hfi a ((a:ℝ)+s))
    change vectorAdditiveState d σ x 1 a sample=x+_+∫u in 0..(a:ℝ),f u at hea
    change X s=x+_+∫u in 0..((a+s.toNNReal:ℝ≥0):ℝ),f u at hes
    rw [NNReal.coe_add,Real.coe_toNNReal s hs.1] at hes
    rw [hi]
    change X s=vectorAdditiveState d σ x 1 a sample+σ •
      vectorContinuousNoise (vectorFutureBrownianPath a sample) s+_
    rw [hn,smul_sub,hea,hes,←hadj]
    abel
  have hu:=vectorNoiseStatePath_unique (vectorTimeShiftDriftData d a) σ
    (vectorRestartHorizon q) z X hX he r ⟨r.coe_nonneg,hr⟩
  simpa only [X,z,a,Real.toNNReal_coe,vectorNoiseRestartStatePath] using hu

end QuantitativePaper
