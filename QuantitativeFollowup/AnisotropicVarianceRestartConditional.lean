module
public import QuantitativeFollowup.AnisotropicVarianceNoiseRestart
public import QuantitativeFollowup.AnisotropicVarianceFutureNoise

@[expose] public section

/-! The fresh anisotropic continuation is the true conditional future
spin square under the native full-past law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def anisotropicRestartNoiseSpinResponse (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q r : Paper.Overlap) (i : Fin n) (z : AnisotropicRestartNoiseData n) : ℝ :=
  anisotropicMeasureTailMagnetization D μ r
    (anisotropicDisorderInjection n z.1.1+anisotropicUnitInput D
      (anisotropicRestartNoiseStatePath D μ q
        ((z.1.1,anisotropicInverseNoiseMap D z.1.2),z.2) ((r:ℝ)-(q:ℝ)))) i

theorem measurable_uncurry_anisotropicRestartNoiseSpinResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (i : Fin n) :
    Measurable (fun z : Paper.Overlap×AnisotropicRestartNoiseData n=>
      anisotropicRestartNoiseSpinResponse D μ q z.1 i z.2) := by
  have ht : Measurable (fun z : Paper.Overlap×AnisotropicRestartNoiseData n=>
      ((z.1:ℝ)-(q:ℝ),((z.2.1.1,anisotropicInverseNoiseMap D z.2.1.2),z.2.2))) := by fun_prop
  have hX:=(measurable_uncurry_anisotropicRestartNoiseStatePath D μ q).comp ht
  have hP:=((anisotropicDisorderInjection n).measurable.comp measurable_snd.fst.fst).add
    ((anisotropicUnitInput D).measurable.comp hX)
  have hM:=(measurable_anisotropicMeasureTailMagnetization D μ).comp (measurable_fst.prodMk hP)
  exact (EuclideanSpace.proj i).measurable.comp hM

theorem anisotropicRestartNoiseSpinResponse_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (i : Fin n)
    (z : AnisotropicRestartNoiseData n) : |anisotropicRestartNoiseSpinResponse D μ q r i z|≤1 :=
  anisotropicMeasureTailMagnetization_component_bound D μ r _ i

def anisotropicRestartConditionalSpinSquare (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (i : Fin n)
    (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  ∫V,(anisotropicRestartNoiseSpinResponse D μ q r i
    ((sample.1,anisotropicMeasureState D μ q sample),V))^2 ∂vectorWienerMeasure n

theorem measurable_uncurry_anisotropicRestartConditionalSpinSquare (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (i : Fin n) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      anisotropicRestartConditionalSpinSquare D μ q z.1 i z.2) := by
  have hX : Measurable (fun z : (Paper.Overlap×AnisotropicDisorderBrownianSample n)×VectorWienerPath n=>
      (z.1.1,((z.1.2.1,anisotropicMeasureState D μ q z.1.2),z.2))) := by
    have harg : Measurable (fun z : (Paper.Overlap×AnisotropicDisorderBrownianSample n)×VectorWienerPath n=>
        ((q:ℝ),z.1.2)) := (measurable_const (a:=(q:ℝ))).prodMk measurable_fst.snd
    have hs0:=(measurable_uncurry_anisotropicMeasureState D μ).comp harg
    have hs : Measurable (fun z : (Paper.Overlap×AnisotropicDisorderBrownianSample n)×VectorWienerPath n=>
        anisotropicMeasureState D μ q z.1.2) := by
      simpa only [Function.comp_def,Function.uncurry_def] using hs0
    exact measurable_fst.fst.prodMk ((measurable_fst.snd.fst.prodMk hs).prodMk measurable_snd)
  have hF:=((measurable_uncurry_anisotropicRestartNoiseSpinResponse D μ q i).comp hX).pow_const 2
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

theorem anisotropicRestartConditionalSpinSquare_eq_restart (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r) (i : Fin n)
    (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicRestartConditionalSpinSquare D μ q r i sample=
      anisotropicRestartSpinSquare D μ sample.1 q (anisotropicMeasureState D μ q sample) i r := by
  let v : ℝ≥0 := ((r:ℝ)-(q:ℝ)).toNNReal
  have hv : v≤vectorRestartHorizon q := Real.toNNReal_le_toNNReal
    (sub_le_sub_right r.property.2 _)
  have hh : HasLaw (fun p : VectorDisorderBrownianSample n=>vectorCanonicalBrownianPath p.2)
      (vectorWienerMeasure n) (vectorDisorderBrownianMeasure n) :=
    hasLaw_vectorCanonicalBrownianPath.comp (hasLaw_vectorBrownian_samples_with_disorder n)
  have hm : Measurable (fun V=>(anisotropicRestartNoiseSpinResponse D μ q r i
      ((sample.1,anisotropicMeasureState D μ q sample),V))^2) :=
    (((measurable_uncurry_anisotropicRestartNoiseSpinResponse D μ q i).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).pow_const 2)
  unfold anisotropicRestartConditionalSpinSquare anisotropicRestartSpinSquare
  rw [←hh.map_eq,integral_map hh.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with p
  unfold anisotropicRestartNoiseSpinResponse anisotropicRestartSpinResponse anisotropicRestartPhysicalParameter
  have he:=anisotropicRestartNoiseStatePath_canonical D μ sample.1 q
    (anisotropicInverseNoiseMap D (anisotropicMeasureState D μ q sample)) v hv p
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr (show (q:ℝ)≤(r:ℝ) from hqr))] at he
  rw [he]

theorem anisotropicRestartConditionalSpinSquare_condExp (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q r : Paper.Overlap) (hqr : q≤r) (i : Fin n) :
    (anisotropicMeasureSampleLaw D μ a)[(fun sample=>(anisotropicProcessSpinResponse D μ r i sample)^2)|
      anisotropicBrownianFiltration n (q:ℝ).toNNReal]=ᵐ[anisotropicMeasureSampleLaw D μ a]
        anisotropicRestartConditionalSpinSquare D μ q r i := by
  let X : AnisotropicDisorderBrownianSample n→AnisotropicDisorder n×Field n :=
    fun sample=>(sample.1,anisotropicMeasureState D μ q sample)
  have hq1 : (q:ℝ).toNNReal≤1 := by simpa using Real.toNNReal_le_toNNReal q.property.2
  have hXs : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal]
      (fun sample=>anisotropicMeasureState D μ q sample) := by
    simpa only [Real.coe_toNNReal _ q.property.1] using adapted_anisotropicMeasureState D μ (q:ℝ).toNNReal hq1
  have hX : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] X :=
    (measurable_anisotropicInitialDisorder _).prodMk hXs
  let f : (AnisotropicDisorder n×Field n)×VectorWienerPath n→ℝ :=
    fun z=>(anisotropicRestartNoiseSpinResponse D μ q r i z)^2
  have hf : Measurable f := ((measurable_uncurry_anisotropicRestartNoiseSpinResponse D μ q i).comp
    (measurable_const.prodMk measurable_id)).pow_const 2
  have hb : ∀z,‖f z‖≤1 := fun z=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff_abs_le_one _).mpr (anisotropicRestartNoiseSpinResponse_bound D μ q r i z)
  have hh:=condExp_independent_noise (anisotropicBrownianFiltration n (q:ℝ).toNNReal)
    (anisotropicMeasureSampleLaw D μ a) ((anisotropicBrownianFiltration n).le _) X hX
    (anisotropicFutureBrownianPath (q:ℝ).toNNReal) (measurable_anisotropicFutureBrownianPath _)
    (vectorWienerMeasure n) (hasLaw_anisotropicFutureBrownianPath D μ a _)
    (indep_anisotropicFutureBrownianPath_filtration D μ a _) f hf 1 hb
  have he : (fun sample=>f (X sample,anisotropicFutureBrownianPath (q:ℝ).toNNReal sample))=
      fun sample=>(anisotropicProcessSpinResponse D μ r i sample)^2 := by
    funext sample
    dsimp only [f,X,anisotropicRestartNoiseSpinResponse,anisotropicFutureBrownianPath]
    have hs:=anisotropicMeasureState_restart D μ q r hqr sample
    change anisotropicMeasureState D μ r sample=anisotropicNoiseMap D
      (anisotropicRestartNoiseStatePath D μ q
        ((sample.1,anisotropicInverseNoiseMap D (anisotropicMeasureState D μ q sample)),
          anisotropicFutureBrownianPath (q:ℝ).toNNReal sample) ((r:ℝ)-(q:ℝ))) at hs
    rw [anisotropicUnitInput,ContinuousLinearMap.comp_apply,←hs]
    rfl
  rw [he] at hh
  exact hh

end QuantitativeFollowup
