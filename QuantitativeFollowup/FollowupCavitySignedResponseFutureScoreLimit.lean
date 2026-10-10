module
public import QuantitativeFollowup.AnisotropicNoiseProfileStability
public import QuantitativeFollowup.AnisotropicFiniteMeasureStateAgreement
public import FourPapersCommon.ProbabilityIntegralContinuity
public import FRSB.ParisiGridTopology
public import FRSB.GridMeasureIdentification

@[expose] public section

/-! Genuine weak-profile convergence of the strict-future score.  The
integrand vanishes at the restart level, so atoms there require no CDF
continuity assumption.  All paths use the same actual Wiener sample. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def cavityRestartSpinVector (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (sample : VectorDisorderBrownianSample n) (r : Paper.Overlap) : Field n :=
  anisotropicMeasureTailMagnetization D μ r
    (anisotropicRestartPhysicalParameter D μ g q x ((r:ℝ)-(q:ℝ)).toNNReal sample)

theorem continuous_cavityRestartSpinVector (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (sample : VectorDisorderBrownianSample n) :
    Continuous (cavityRestartSpinVector D μ g q x sample) := by
  have ht : Continuous (fun r : Paper.Overlap=>((r:ℝ)-(q:ℝ)).toNNReal) := by fun_prop
  have hX := (continuous_anisotropicRestartState D μ g q
    (anisotropicInverseNoiseMap D x) sample).comp ht
  have hP := (continuous_const (y:=anisotropicDisorderInjection n g)).add
    ((anisotropicUnitInput D).continuous.comp hX)
  have h := (continuous_anisotropicMeasureTailMagnetization_joint D μ).comp (continuous_id.prodMk hP)
  dsimp only [Function.comp_def] at h
  change Continuous (fun r : Paper.Overlap=>anisotropicMeasureTailMagnetization D μ r
    (anisotropicDisorderInjection n g+anisotropicUnitInput D
      (anisotropicRestartState D μ g q (anisotropicInverseNoiseMap D x)
        ((r:ℝ)-(q:ℝ)).toNNReal sample)))
  simpa only [Pi.add_apply,id_eq] using h

def cavityRestartSpinProfileError (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) : ℝ :=
  anisotropicProfileGradientError D μ ν+
    (‖anisotropicResponseMap n‖*‖anisotropicEnergyMap D‖^2)*‖anisotropicUnitInput D‖*
      (anisotropicNoiseProfileError D μ ν*Real.exp (anisotropicWhitenedDriftLip D))

theorem norm_cavityRestartSpinVector_profile_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (sample : VectorDisorderBrownianSample n) (r : Paper.Overlap)
    (hqr : q≤r) :
    ‖cavityRestartSpinVector D μ g q x sample r-cavityRestartSpinVector D ν g q x sample r‖≤
      cavityRestartSpinProfileError D μ ν := by
  let t : ℝ≥0:=((r:ℝ)-(q:ℝ)).toNNReal
  have ht : (t:ℝ)=(r:ℝ)-(q:ℝ) := Real.coe_toNNReal _ (sub_nonneg.mpr hqr)
  have hti : t≤vectorRestartHorizon q := Real.toNNReal_le_toNNReal (sub_le_sub_right r.property.2 _)
  have hstate := norm_anisotropicRestartNoiseStatePath_profile_sub_le D μ ν g q
    (anisotropicInverseNoiseMap D x) (anisotropicInverseNoiseMap D x)
    (vectorCanonicalBrownianPath sample.2) t ⟨t.coe_nonneg,by rw [ht];linarith [r.property.2]⟩
  rw [anisotropicRestartNoiseStatePath_canonical D μ g q _ t hti sample,
    anisotropicRestartNoiseStatePath_canonical D ν g q _ t hti sample] at hstate
  simp only [sub_self,norm_zero,zero_add] at hstate
  let P := anisotropicRestartPhysicalParameter D μ g q x t sample
  let Q := anisotropicRestartPhysicalParameter D ν g q x t sample
  have hPQ : ‖P-Q‖≤‖anisotropicUnitInput D‖*
      (anisotropicNoiseProfileError D μ ν*Real.exp (anisotropicWhitenedDriftLip D)) := by
    change ‖(_+anisotropicUnitInput D _)-(_+anisotropicUnitInput D _)‖≤_
    rw [add_sub_add_left_eq_sub,←map_sub]
    exact ((anisotropicUnitInput D).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hstate (norm_nonneg _))
  have hLip := (anisotropicMeasureTailMagnetization_lipschitz D ν r).dist_le_mul P Q
  simp only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_pow,coe_nnnorm] at hLip
  have hp := norm_anisotropicMeasureTailMagnetization_profile_sub_le D μ ν r P
  change ‖anisotropicMeasureTailMagnetization D μ r P-anisotropicMeasureTailMagnetization D ν r Q‖≤_
  calc
    _≤‖anisotropicMeasureTailMagnetization D μ r P-anisotropicMeasureTailMagnetization D ν r P‖+
        ‖anisotropicMeasureTailMagnetization D ν r P-anisotropicMeasureTailMagnetization D ν r Q‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤anisotropicProfileGradientError D μ ν+
        (‖anisotropicResponseMap n‖*‖anisotropicEnergyMap D‖^2)*(‖anisotropicUnitInput D‖*
          (anisotropicNoiseProfileError D μ ν*Real.exp (anisotropicWhitenedDriftLip D))) :=
      add_le_add hp (hLip.trans (mul_le_mul_of_nonneg_left hPQ (by positivity)))
    _=cavityRestartSpinProfileError D μ ν := by unfold cavityRestartSpinProfileError;ring

def cavityRestartStrictFutureResidual (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (sample : VectorDisorderBrownianSample n) (r : Paper.Overlap) : ℝ :=
  inner ℝ w (cavityRestartSpinVector D μ g q x sample (max q r)-
    cavityRestartSpinVector D μ g q x sample q)

theorem cavityRestartStrictFutureResidual_eq (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x w : Field n) (sample : VectorDisorderBrownianSample n) (r : Paper.Overlap) :
    cavityRestartStrictFutureResidual D μ g q x w sample r=
      if q<r then inner ℝ w (cavityRestartSpinVector D μ g q x sample r-
        cavityRestartSpinVector D μ g q x sample q) else 0 := by
  by_cases h : q<r
  · simp [cavityRestartStrictFutureResidual,h,max_eq_right h.le]
  · simp [cavityRestartStrictFutureResidual,h,max_eq_left (le_of_not_gt h)]

theorem continuous_cavityRestartStrictFutureResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x w : Field n) (sample : VectorDisorderBrownianSample n) :
    Continuous (cavityRestartStrictFutureResidual D μ g q x w sample) :=
  continuous_const.inner ((continuous_cavityRestartSpinVector D μ g q x sample).comp
    (continuous_const.max continuous_id) |>.sub continuous_const)

theorem norm_cavityRestartStrictFutureResidual_profile_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x w : Field n) (sample : VectorDisorderBrownianSample n) (r : Paper.Overlap) :
    ‖cavityRestartStrictFutureResidual D μ g q x w sample r-
      cavityRestartStrictFutureResidual D ν g q x w sample r‖≤
      (2*‖w‖)*cavityRestartSpinProfileError D μ ν := by
  unfold cavityRestartStrictFutureResidual
  rw [←inner_sub_right]
  have he : (cavityRestartSpinVector D μ g q x sample (max q r)-cavityRestartSpinVector D μ g q x sample q)-
      (cavityRestartSpinVector D ν g q x sample (max q r)-cavityRestartSpinVector D ν g q x sample q)=
      (cavityRestartSpinVector D μ g q x sample (max q r)-cavityRestartSpinVector D ν g q x sample (max q r))-
      (cavityRestartSpinVector D μ g q x sample q-cavityRestartSpinVector D ν g q x sample q) := by abel
  rw [he]
  apply (norm_inner_le_norm _ _).trans
  have hb := (norm_sub_le _ _).trans (add_le_add
    (norm_cavityRestartSpinVector_profile_sub_le D μ ν g q x sample (max q r) (le_max_left _ _))
    (norm_cavityRestartSpinVector_profile_sub_le D μ ν g q x sample q le_rfl))
  calc
    _≤‖w‖*(cavityRestartSpinProfileError D μ ν+cavityRestartSpinProfileError D μ ν) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _=_ := by ring

theorem tendsto_cavityRestartSpinProfileError {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure} (hμ : Tendsto μ l (𝓝 ν)) :
    Tendsto (fun j=>cavityRestartSpinProfileError D (μ j) ν) l (𝓝 0) := by
  have hd := FRSB.tendsto_parisiCDFDistance_of_tendsto hμ
  have hg := tendsto_anisotropicProfileGradientError D μ ν hd
  have hn := tendsto_anisotropicNoiseProfileError D μ ν hd
  have h := hg.add ((hn.mul_const (Real.exp (anisotropicWhitenedDriftLip D))).const_mul
    ((‖anisotropicResponseMap n‖*‖anisotropicEnergyMap D‖^2)*‖anisotropicUnitInput D‖))
  simpa only [cavityRestartSpinProfileError,zero_mul,mul_zero,add_zero] using h

theorem tendstoUniformlyOn_cavityRestartSpinVector_profile {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure} (hμ : Tendsto μ l (𝓝 ν))
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (sample : VectorDisorderBrownianSample n) :
    TendstoUniformlyOn (fun j=>cavityRestartSpinVector D (μ j) g q x sample)
      (cavityRestartSpinVector D ν g q x sample) l (Ici q) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_cavityRestartSpinProfileError D hμ).eventually (gt_mem_nhds hε)] with j hj
  intro r hr
  rw [dist_eq_norm,norm_sub_rev]
  exact (norm_cavityRestartSpinVector_profile_sub_le D (μ j) ν g q x sample r hr).trans_lt hj

theorem tendsto_cavityRestartStrictFutureResidual_integral {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure} (hμ : Tendsto μ l (𝓝 ν))
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    Tendsto (fun j=>∫r,cavityRestartStrictFutureResidual D (μ j) g q x w sample r
      ∂(μ j:Measure Paper.Overlap)) l
      (𝓝 (∫r,cavityRestartStrictFutureResidual D ν g q x w sample r ∂(ν:Measure Paper.Overlap))) := by
  let F : C(Paper.Overlap,ℝ) := ⟨cavityRestartStrictFutureResidual D ν g q x w sample,
    continuous_cavityRestartStrictFutureResidual D ν g q x w sample⟩
  have hfixed := (ProbabilityMeasure.continuous_integral_continuousMap F).tendsto ν |>.comp hμ
  have he := (tendsto_cavityRestartSpinProfileError D hμ).const_mul (2*‖w‖)
  simp only [mul_zero] at he
  have hbound (j : L) :
      ‖(∫r,cavityRestartStrictFutureResidual D (μ j) g q x w sample r ∂(μ j:Measure Paper.Overlap))-
        (∫r,F r ∂(μ j:Measure Paper.Overlap))‖≤(2*‖w‖)*cavityRestartSpinProfileError D (μ j) ν := by
    have hj : Integrable (cavityRestartStrictFutureResidual D (μ j) g q x w sample)
        (μ j:Measure Paper.Overlap) :=
      continuousMap_integrable_probability ⟨_,continuous_cavityRestartStrictFutureResidual D (μ j) g q x w sample⟩ (μ j)
    rw [←integral_sub hj (continuousMap_integrable_probability F (μ j))]
    have h := norm_integral_le_of_norm_le_const (μ:=(μ j:Measure Paper.Overlap))
      (.of_forall fun r=>norm_cavityRestartStrictFutureResidual_profile_sub_le D (μ j) ν g q x w sample r)
    simpa only [probReal_univ,mul_one,F,ContinuousMap.coe_mk] using h
  have herror := squeeze_zero (fun j=>norm_nonneg _) hbound he
  exact tendsto_of_tendsto_of_dist hfixed (by simpa only [dist_eq_norm,norm_sub_rev,Function.comp_def] using herror)

theorem tendsto_cavityRestartStrictFutureResidual_dyadic (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x w : Field n) (sample : VectorDisorderBrownianSample n) :
    Tendsto (fun j=>∫r,cavityRestartStrictFutureResidual D
      (Paper.parisiSchemeMeasure (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)))
      g q x w sample r
      ∂(Paper.parisiSchemeMeasure (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)):Measure Paper.Overlap))
      atTop (𝓝 (∫r,cavityRestartStrictFutureResidual D μ g q x w sample r ∂(μ:Measure Paper.Overlap))) := by
  apply tendsto_cavityRestartStrictFutureResidual_integral
  simp_rw [FRSB.parisiSchemeMeasure_grid_eq]
  exact (FRSB.tendsto_parisiGridMeasure μ).comp tendsto_vectorDyadicIndex

end QuantitativeFollowup
