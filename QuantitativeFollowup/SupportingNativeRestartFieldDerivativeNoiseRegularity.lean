module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeNoise

@[expose] public section

/-! Actual measurability and uniform bounds of the entire future-score
functional on the genuine restart noise space. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 180000
set_option maxSynthPendingDepth 128

theorem measurable_uncurry_cavityRestartNoiseMean (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Measurable (fun z : Paper.Overlap×AnisotropicRestartNoiseData n=>cavityRestartNoiseMean D μ q z.1 z.2) := by
  have h:=(measurable_anisotropicMeasureTailMagnetization D μ).comp
    (measurable_fst.prodMk (measurable_uncurry_cavityRestartNoiseParameter D μ q))
  dsimp only [Function.comp_def] at h
  exact h

theorem measurable_cavityRestartInitialMean (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) : Measurable (cavityRestartInitialMean D μ q) := by
  have h:=(measurable_anisotropicMeasureTailMagnetization D μ).comp
    ((measurable_const (a:=q)).prodMk (((anisotropicDisorderInjection n).measurable.comp measurable_fst).add
      ((anisotropicFieldInjection n).measurable.comp measurable_snd)))
  convert h using 1
  funext z
  rfl

theorem measurable_uncurry_cavityRestartNoiseResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Measurable (fun z : Paper.Overlap×AnisotropicRestartNoiseData n=>cavityRestartNoiseResidual D μ q z.1 z.2) := by
  classical
  have hm : Measurable (fun z : Paper.Overlap×AnisotropicRestartNoiseData n=>cavityRestartInitialMean D μ q z.2.1):=
    (measurable_cavityRestartInitialMean D μ q).comp measurable_snd.fst
  have h : Measurable (fun z : Paper.Overlap×AnisotropicRestartNoiseData n=>
      if q<z.1 then inner ℝ (cavityRestartInitialMean D μ q z.2.1)
        (cavityRestartNoiseMean D μ q z.1 z.2-cavityRestartInitialMean D μ q z.2.1) else 0) :=
    Measurable.ite (measurableSet_lt (measurable_const (a:=q)) measurable_fst)
      (hm.inner (𝕜:=ℝ) ((measurable_uncurry_cavityRestartNoiseMean D μ q).sub hm)) measurable_const
  convert h using 1
  funext z
  rfl

theorem measurable_cavityRestartNoiseSquareResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (i : Fin n) :
    Measurable (cavityRestartNoiseSquareResponse D μ q r i) := by
  have hm:=(measurable_uncurry_cavityRestartNoiseMean D μ q).comp
    ((measurable_const (a:=r)).prodMk (measurable_id (α:=AnisotropicRestartNoiseData n)))
  dsimp only [Function.comp_def] at hm
  have hmc:=(EuclideanSpace.proj i).measurable.comp hm
  have hw : Measurable (fun z : AnisotropicRestartNoiseData n=>cavityRestartInitialMean D μ q z.1):=
    (measurable_cavityRestartInitialMean D μ q).comp measurable_fst
  have hp:=(measurable_uncurry_cavityRestartNoiseParameter D μ q).comp
    ((measurable_const (a:=r)).prodMk (measurable_id (α:=AnisotropicRestartNoiseData n)))
  dsimp only [Function.comp_def] at hp
  have hT:=(continuous_anisotropicMeasureTailSecondDifferential_joint D μ).measurable.comp
    ((measurable_const (a:=r)).prodMk hp)
  have hev : Continuous (fun z : ((AnisotropicParameter n→L[ℝ](AnisotropicParameter n→L[ℝ]ℝ))×
      AnisotropicParameter n)×AnisotropicParameter n=>z.1.1 z.1.2 z.2) :=
    (continuous_fst.fst.clm_apply continuous_fst.snd).clm_apply continuous_snd
  have hH:=hev.measurable.comp ((hT.prodMk ((anisotropicFieldInjection n).measurable.comp hw)).prodMk (measurable_const (a:=anisotropicCoordinateDirection n i)))
  have h1:=(measurable_uncurry_cavityRestartNoiseMean D μ q).comp
    ((measurable_const (a:=(1:Paper.Overlap))).prodMk (measurable_id (α:=AnisotropicRestartNoiseData n)))
  dsimp only [Function.comp_def] at h1
  have hI:=((measurable_uncurry_cavityRestartNoiseResidual D μ q).stronglyMeasurable.integral_prod_left'
    (μ:=(μ:Measure Paper.Overlap))).measurable
  have h:=((hmc.const_mul 2).mul hH).add ((hmc.pow_const 2).mul ((hw.inner (𝕜:=ℝ) (h1.sub hw)).sub hI))
  convert h using 1
  funext z
  rfl

def cavityRestartNoiseHessianBound (D : AnisotropicSpinModel n) (i : Fin n) : ℝ :=
  ‖anisotropicEnergyMap D‖^2*‖anisotropicFieldInjection n‖*Real.sqrt (n:ℝ)*‖anisotropicCoordinateDirection n i‖

def cavityRestartNoiseSquareBound (D : AnisotropicSpinModel n) (i : Fin n) : ℝ :=
  2*cavityRestartNoiseHessianBound D i+4*(Real.sqrt (n:ℝ))^2

theorem norm_cavityRestartNoiseResidual_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q u : Paper.Overlap) (z : AnisotropicRestartNoiseData n) :
    ‖cavityRestartNoiseResidual D μ q u z‖≤2*(Real.sqrt (n:ℝ))^2 := by
  have hw:=norm_anisotropicMeasureTailMagnetization_le D μ q
    (anisotropicDisorderInjection n z.1.1+anisotropicFieldInjection n z.1.2)
  have hu:=norm_anisotropicMeasureTailMagnetization_le D μ u (cavityRestartNoiseParameter D μ q u z)
  change ‖cavityRestartInitialMean D μ q z.1‖≤Real.sqrt (n:ℝ) at hw
  change ‖cavityRestartNoiseMean D μ q u z‖≤Real.sqrt (n:ℝ) at hu
  unfold cavityRestartNoiseResidual
  split_ifs
  · calc
      _≤‖cavityRestartInitialMean D μ q z.1‖*
          (‖cavityRestartNoiseMean D μ q u z‖+‖cavityRestartInitialMean D μ q z.1‖) :=
        (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
      _≤Real.sqrt (n:ℝ)*(Real.sqrt (n:ℝ)+Real.sqrt (n:ℝ)) :=
        mul_le_mul hw (add_le_add hu hw) (by positivity) (Real.sqrt_nonneg _)
      _=_ := by ring
  · simp only [norm_zero]; positivity

theorem norm_cavityRestartNoiseSquareResponse_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (i : Fin n) (z : AnisotropicRestartNoiseData n) :
    ‖cavityRestartNoiseSquareResponse D μ q r i z‖≤cavityRestartNoiseSquareBound D i := by
  let T:=fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ r)) (cavityRestartNoiseParameter D μ q r z)
  let w:=cavityRestartInitialMean D μ q z.1
  have hm : ‖cavityRestartNoiseMean D μ q r z i‖≤1 := by
    simpa only [Real.norm_eq_abs,cavityRestartNoiseMean] using anisotropicMeasureTailMagnetization_component_bound D μ r _ i
  have hw : ‖w‖≤Real.sqrt (n:ℝ):=norm_anisotropicMeasureTailMagnetization_le D μ q _
  have hT : ‖T‖≤‖anisotropicEnergyMap D‖^2:=norm_anisotropicMeasureTailSecondDifferential_le D μ r _
  have hW : ‖anisotropicFieldInjection n w‖≤‖anisotropicFieldInjection n‖*Real.sqrt (n:ℝ):=
    ((anisotropicFieldInjection n).le_opNorm w).trans
      (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
  have hH : ‖T (anisotropicFieldInjection n w) (anisotropicCoordinateDirection n i)‖≤
      cavityRestartNoiseHessianBound D i := by
    calc
      _≤‖T‖*‖anisotropicFieldInjection n w‖*‖anisotropicCoordinateDirection n i‖ :=
        ((T _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _))
      _≤_ := by
        unfold cavityRestartNoiseHessianBound
        exact (mul_le_mul_of_nonneg_right (mul_le_mul hT hW (norm_nonneg _) (by positivity)) (norm_nonneg _)).trans_eq (by ring)
  have hs : ‖inner ℝ w (cavityRestartNoiseMean D μ q 1 z-w)‖≤2*(Real.sqrt (n:ℝ))^2 := by
    calc
      _≤‖w‖*(‖cavityRestartNoiseMean D μ q 1 z‖+‖w‖):=
        (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
      _≤Real.sqrt (n:ℝ)*(Real.sqrt (n:ℝ)+Real.sqrt (n:ℝ)):=
        mul_le_mul hw (add_le_add (norm_anisotropicMeasureTailMagnetization_le D μ 1 _) hw) (by positivity) (Real.sqrt_nonneg _)
      _=_ := by ring
  have hI : ‖∫u,cavityRestartNoiseResidual D μ q u z ∂(μ:Measure Paper.Overlap)‖≤2*(Real.sqrt (n:ℝ))^2 := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=(μ:Measure Paper.Overlap))
      (.of_forall fun u=>norm_cavityRestartNoiseResidual_le D μ q u z)
  have hscore : ‖inner ℝ w (cavityRestartNoiseMean D μ q 1 z-w)-
      ∫u,cavityRestartNoiseResidual D μ q u z ∂(μ:Measure Paper.Overlap)‖≤4*(Real.sqrt (n:ℝ))^2 :=
    (norm_sub_le _ _).trans ((add_le_add hs hI).trans_eq (by ring))
  have hfirst : ‖2*(cavityRestartNoiseMean D μ q r z i)*T (anisotropicFieldInjection n w) (anisotropicCoordinateDirection n i)‖≤
      2*cavityRestartNoiseHessianBound D i := by
    rw [norm_mul,norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num)) hH (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hsecond : ‖(cavityRestartNoiseMean D μ q r z i)^2*
      (inner ℝ w (cavityRestartNoiseMean D μ q 1 z-w)-∫u,cavityRestartNoiseResidual D μ q u z ∂(μ:Measure Paper.Overlap))‖≤
      4*(Real.sqrt (n:ℝ))^2 := by
    rw [norm_mul,norm_pow]
    exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hm 2) hscore (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

end QuantitativeFollowup
