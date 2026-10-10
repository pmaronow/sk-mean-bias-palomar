module
public import QuantitativePaper.VectorNoiseRestart
public import QuantitativePaper.BrownianIndependentConditionalMean

@[expose] public section

/-! The pathwise restart gives honest conditional averaging under the full
initial-disorder/Wiener past, and agrees with the constructed fresh diffusion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorNoiseRestartStatePath_canonical (d : VectorAdditiveDriftData n)
    (σ : ℝ) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (sample : VectorDisorderBrownianSample n) (r : ℝ≥0) (hr : r≤vectorRestartHorizon q) :
    vectorNoiseRestartStatePath d σ q ((p,x),vectorCanonicalBrownianPath sample.2) r=
      vectorAdditiveState (vectorFixedRestartDriftData d (q:ℝ).toNNReal p) σ x
        (vectorRestartHorizon q) r sample := by
  apply vectorAdditiveState_unique _ σ x (vectorRestartHorizon q) sample
    (fun s=>vectorNoiseRestartStatePath d σ q ((p,x),vectorCanonicalBrownianPath sample.2) s)
    ((continuous_vectorNoiseStatePath _ σ _ _).comp NNReal.continuous_coe) ?_ r hr
  intro u hu
  rw [vectorIntegral_Ioc_eq_interval]
  have hu1 : u≤1 := by
    have hH : vectorRestartHorizon q≤1 := by
      simpa only [vectorRestartHorizon,Real.toNNReal_one] using
        Real.toNNReal_le_toNNReal (show 1-(q:ℝ)≤1 by linarith [q.property.1])
    exact hu.trans hH
  have he:=vectorNoiseStatePath_equation (vectorTimeShiftDriftData d (q:ℝ).toNNReal) σ
    (vectorRestartHorizon q) ((p,x),vectorCanonicalBrownianPath sample.2) u ⟨u.coe_nonneg,hu⟩
  rw [vectorContinuousNoise_canonical sample u hu1] at he
  change vectorNoiseRestartStatePath d σ q ((p,x),vectorCanonicalBrownianPath sample.2) u=
    x+σ • disorderVectorBrownian u sample+_ at he
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le u.coe_nonneg] at hs
  dsimp only [vectorTimeShiftDriftData,vectorFixedRestartDriftData,vectorNoiseRestartStatePath]
  rw [Real.coe_toNNReal s hs.1]

theorem integral_vectorNoiseRestartStatePath_eq_fresh (d : VectorAdditiveDriftData n)
    (σ : ℝ) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (r : ℝ≥0) (hr : r≤vectorRestartHorizon q) (f : Field n→ℝ) (hf : Measurable f) :
    (∫V,f (vectorNoiseRestartStatePath d σ q ((p,x),V) r) ∂vectorWienerMeasure n)=
      ∫sample,f (vectorAdditiveState (vectorFixedRestartDriftData d (q:ℝ).toNNReal p)
        σ x (vectorRestartHorizon q) r sample) ∂vectorDisorderBrownianMeasure n := by
  have hh : HasLaw (fun sample : VectorDisorderBrownianSample n=>vectorCanonicalBrownianPath sample.2)
      (vectorWienerMeasure n) (vectorDisorderBrownianMeasure n) :=
    hasLaw_vectorCanonicalBrownianPath.comp (hasLaw_vectorBrownian_samples_with_disorder n)
  have hm : Measurable (fun V=>f (vectorNoiseRestartStatePath d σ q ((p,x),V) r)) :=
    hf.comp ((measurable_uncurry_vectorNoiseRestartStatePath d σ q).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  rw [←hh.map_eq,integral_map hh.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun sample=>congrArg f (vectorNoiseRestartStatePath_canonical d σ q p x sample r hr)

theorem condExp_vectorAdditiveState_future (d : VectorAdditiveDriftData n)
    (σ : ℝ) (x : Field n) (q : Paper.Overlap) (r : ℝ≥0) (hr : r≤vectorRestartHorizon q)
    (f : (Couplings n×ℝ)×Field n→ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀z,‖f z‖≤C) :
    (vectorDisorderBrownianMeasure n)[(fun sample=>f (sample.1,
      vectorAdditiveState d σ x 1 ((q:ℝ).toNNReal+r) sample))|
        vectorBrownianFiltration n (q:ℝ).toNNReal]=ᵐ[vectorDisorderBrownianMeasure n]
      fun sample=>∫V,f (sample.1,vectorNoiseRestartStatePath d σ q
        ((sample.1,vectorAdditiveState d σ x 1 (q:ℝ).toNNReal sample),V) r)
          ∂vectorWienerMeasure n := by
  let X : VectorDisorderBrownianSample n→(Couplings n×ℝ)×Field n :=
    fun sample=>(sample.1,vectorAdditiveState d σ x 1 (q:ℝ).toNNReal sample)
  have hX : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] X :=
    (stronglyMeasurable_initialVectorDisorder n _).measurable.prodMk
      (stronglyAdapted_vectorAdditiveState d σ x 1 _).measurable
  let g : ((Couplings n×ℝ)×Field n)×VectorWienerPath n→ℝ :=
    fun z=>f (z.1.1,vectorNoiseRestartStatePath d σ q (z.1,z.2) r)
  have hg : Measurable g := hf.comp (measurable_fst.fst.prodMk
    ((measurable_uncurry_vectorNoiseRestartStatePath d σ q).comp
      (measurable_const.prodMk measurable_id)))
  have hh:=condExp_independent_noise (vectorBrownianFiltration n (q:ℝ).toNNReal)
    (vectorDisorderBrownianMeasure n) ((vectorBrownianFiltration n).le _) X hX
    (vectorFutureBrownianPath (q:ℝ).toNNReal) (measurable_vectorFutureBrownianPath _)
    (vectorWienerMeasure n) (hasLaw_vectorFutureBrownianPath _)
    (indep_vectorFutureBrownianPath_filtration _) g hg C (fun z=>hC _)
  have he : (fun sample=>g (X sample,vectorFutureBrownianPath (q:ℝ).toNNReal sample))=
      fun sample=>f (sample.1,vectorAdditiveState d σ x 1 ((q:ℝ).toNNReal+r) sample) := by
    funext sample
    dsimp only [g,X]
    rw [←vectorAdditiveState_restart d σ x q sample r hr]
  rw [he] at hh
  exact hh

end QuantitativePaper
