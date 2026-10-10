module
public import QuantitativePaper.VectorFixedStateGradientSourceRegularity
public import QuantitativePaper.VectorTiltedIntegral
public import FourPapersCommon.BoundedTimeInterval
public import FourPapersCommon.LocalItoEndpoints

@[expose] public section

/-! Actual fractional-tilt expectations of finite gradients and their true
Itô source on a fixed arbitrary-profile diffusion. Unbounded initial tilt
weights are discharged by integrable truncation, not assumed bounded. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def vectorFixedStateCellSquareMoment (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (r : ℝ) : ℝ :=
  ∫sample,(gradient (vectorFiniteCellPotential s β t sample.1 i r.toNNReal)
    (vectorMeasureState μ β t ht r.toNNReal sample) l)^2∂vectorMeasureDisorderTilt μ β t outer

def vectorFixedStateCellEnergyMean (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (r : ℝ) : ℝ :=
  ∫sample,vectorFixedStateCellGradientEnergy s μ β t ht i r.toNNReal sample l
    ∂vectorMeasureDisorderTilt μ β t outer

def vectorFixedStateCellSourceMean (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (r : ℝ) : ℝ :=
  ∫sample,vectorFixedStateCellGradientSquareSource s μ β t ht i r.toNNReal sample l
    ∂vectorMeasureDisorderTilt μ β t outer

theorem continuous_vectorFixedStateCellSquareMoment (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) :
    Continuous (vectorFixedStateCellSquareMoment s μ β t outer ht i l) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t outer ht
  apply continuous_of_dominated (μ:=vectorMeasureDisorderTilt μ β t outer) (bound:=fun _=>(1:ℝ))
  · intro r
    exact ((measurable_vectorFixedStateCellGradient s μ β t ht i l r.toNNReal).pow_const 2).aestronglyMeasurable
  · intro r
    exact .of_forall fun sample=>by
      rw [norm_pow,Real.norm_eq_abs]
      exact pow_le_one₀ (n:=2) (abs_nonneg _) (abs_vectorFiniteCellGradient_component_global s β t sample.1 i _ _ l)
  · exact integrable_const _
  · exact .of_forall fun sample=>((continuous_vectorFixedStateCellGradient_path s μ β t ht i l sample).comp
      continuous_real_toNNReal).pow 2

theorem continuous_vectorFixedStateCellEnergyMean (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) :
    Continuous (vectorFixedStateCellEnergyMean s μ β t outer ht i l) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t outer ht
  apply continuous_of_dominated (μ:=vectorMeasureDisorderTilt μ β t outer)
    (bound:=fun _=>(n:ℝ)*(vectorFiniteCellGradientDerivativeBound s β t i l:ℝ)^2)
  · intro r
    exact (measurable_vectorFixedStateCellGradientEnergy s μ β t ht i l r.toNNReal).aestronglyMeasurable
  · intro r
    exact .of_forall fun sample=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (vectorFixedStateCellGradientEnergy_nonneg_le s μ β t ht i l _ sample).1]
      exact (vectorFixedStateCellGradientEnergy_nonneg_le s μ β t ht i l _ sample).2
  · exact integrable_const _
  · exact .of_forall fun sample=>(continuous_vectorFixedStateCellGradientEnergy_path s μ β t ht i l sample).comp
      continuous_real_toNNReal

theorem vectorFixedStateCellSourceMean_intervalIntegrable (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1) (l : Fin n) (a b : ℝ) :
    IntervalIntegrable (vectorFixedStateCellSourceMean s μ β t outer ht i l) volume a b := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t outer ht
  let source:ℝ→VectorDisorderBrownianSample n→ℝ:=fun r sample=>
    vectorFixedStateCellGradientSquareSource s μ β t ht i r.toNNReal sample l
  have hmap:Measurable (fun z : ℝ×VectorDisorderBrownianSample n=>(z.1.toNNReal,z.2)):=
    measurable_real_toNNReal.prodMap measurable_id
  have hm:=(measurable_uncurry_vectorFixedStateCellGradientSquareSource s μ β t ht i l).comp hmap
  dsimp only [Function.comp_def] at hm
  have hmeanm:Measurable (fun r : ℝ=>∫sample,source r sample∂vectorMeasureDisorderTilt μ β t outer):=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  let B:ℝ:=((1-t)*β^2)*(4*(vectorFiniteCellGradientDerivativeBound s β t i l:ℝ)*Real.sqrt n+
      (n:ℝ)*(vectorFiniteCellGradientDerivativeBound s β t i l:ℝ)^2)
  apply (intervalIntegrable_const (c:=B)).mono_fun' hmeanm.aestronglyMeasurable
  exact .of_forall fun r=>by
    change ‖∫sample,source r sample∂vectorMeasureDisorderTilt μ β t outer‖≤B
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=vectorMeasureDisorderTilt (n:=n) μ β t outer)
      (.of_forall (norm_vectorFixedStateCellGradientSquareSource_le s μ β t ht i hi l r.toNNReal))

theorem vectorFixedState_gradient_square_tilted_cropped (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1) (l : Fin n)
    (a b : ℝ≥0) (hab : a≤b) (hb : (b:ℝ)<s.q (i+1)) :
    vectorFixedStateCellSquareMoment s μ β t outer ht.le i l b-
      vectorFixedStateCellSquareMoment s μ β t outer ht.le i l a=
      ∫r in (a:ℝ)..(b:ℝ),vectorFixedStateCellSourceMean s μ β t outer ht.le i l r := by
  let P:=vectorDisorderBrownianMeasure n
  let Q:=vectorMeasureDisorderTilt (n:=n) μ β t outer
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t outer ht.le
  let g:ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>
    gradient (vectorFiniteCellPotential s β t sample.1 i r) (vectorMeasureState μ β t ht.le r sample) l
  let source:ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>
    vectorFixedStateCellGradientSquareSource s μ β t ht.le i r sample l
  let B:ℝ:=((1-t)*β^2)*(4*(vectorFiniteCellGradientDerivativeBound s β t i l:ℝ)*Real.sqrt n+
    (n:ℝ)*(vectorFiniteCellGradientDerivativeBound s β t i l:ℝ)^2)
  have hsb:∀r sample,‖source r sample‖≤B:=norm_vectorFixedStateCellGradientSquareSource_le s μ β t ht.le i hi l
  have hsm:Measurable (Function.uncurry source):=measurable_uncurry_vectorFixedStateCellGradientSquareSource s μ β t ht.le i l
  let F:=fun sample=>g b sample^2-g a sample^2
  let H:=fun sample=>∫r in Ioc a b,source r sample∂nonnegativeLebesgueMeasure
  let W:=fun sample : VectorDisorderBrownianSample n=>Real.exp (outer*vectorMeasurePotential μ β t sample.1 0)
  have hWpast:Measurable[vectorBrownianFiltration n 0] W:=
    (Real.measurable_exp.comp (measurable_const.mul (measurable_vectorMeasurePotential_initial μ β t ht.le))).comp
      (stronglyMeasurable_initialVectorDisorder n 0).measurable
  have hWm:Measurable W:=hWpast.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hWn:∀sample,0≤W sample:=fun _=>(Real.exp_pos _).le
  have hWi:Integrable W P:=(integrable_exp_vectorMeasurePotential μ β t ht.le outer (0:Field n)).comp_fst (vectorBrownianMeasure n)
  have hFm:Measurable F:=((measurable_vectorFixedStateCellGradient s μ β t ht.le i l b).pow_const 2).sub
    ((measurable_vectorFixedStateCellGradient s μ β t ht.le i l a).pow_const 2)
  have hFb:∀sample,‖F sample‖≤2:=fun sample=>by
    have ha:=abs_vectorFiniteCellGradient_component_global s β t sample.1 i a
      (vectorMeasureState μ β t ht.le a sample) l
    have hb:=abs_vectorFiniteCellGradient_component_global s β t sample.1 i b
      (vectorMeasureState μ β t ht.le b sample) l
    dsimp [F,g]
    calc
      _≤‖(gradient (vectorFiniteCellPotential s β t sample.1 i b)
          (vectorMeasureState μ β t ht.le b sample) l)^2‖+
        ‖(gradient (vectorFiniteCellPotential s β t sample.1 i a)
          (vectorMeasureState μ β t ht.le a sample) l)^2‖:=norm_sub_le _ _
      _≤1+1:=add_le_add (by simpa only [norm_pow,Real.norm_eq_abs] using pow_le_one₀ (n:=2) (abs_nonneg _) hb)
        (by simpa only [norm_pow,Real.norm_eq_abs] using pow_le_one₀ (n:=2) (abs_nonneg _) ha)
      _=2:=by norm_num
  have hHm:Measurable H:=measurable_nnreal_intervalIntegral source hsm a b
  have hHb:∀sample,‖H sample‖≤B*max ((b:ℝ)-a) 0:=norm_nnreal_intervalIntegral_le source a b B hsb
  have he:(∫sample,W sample*F sample∂P)=∫sample,W sample*H sample∂P := by
    apply integral_eq_of_truncated_weight_identity P F H W hFm hHm 2 (B*max ((b:ℝ)-a) 0) hFb hHb hWm hWn hWi
    intro j
    have hZ:Measurable[vectorBrownianFiltration n 0] (truncateWeight W j):=
      measurable_const.min hWpast
    have hh:=(vectorFixedState_gradient_square_cropped s μ β t hβ ht i l a b hab hb
      (truncateWeight W j) hZ (j:ℝ≥0)
      (norm_truncateWeight_le W hWn j)).2
    simp only [integral_const_mul] at hh
    exact hh
  have heQ:(∫sample,F sample∂Q)=∫sample,H sample∂Q:=by
    rw [integral_vectorMeasureDisorderTilt μ β t outer ht.le,
      integral_vectorMeasureDisorderTilt μ β t outer ht.le]
    exact congrArg (fun x=>x/vectorMeasureOuterPartition (n:=n) μ β t outer) he
  have hig (r : ℝ≥0) : Integrable (fun sample=>g r sample^2) Q:=
    (integrable_const (1:ℝ)).mono'
      ((measurable_vectorFixedStateCellGradient s μ β t ht.le i l r).pow_const 2).aestronglyMeasurable
      (.of_forall fun sample=>by
        simpa only [norm_pow,Real.norm_eq_abs] using pow_le_one₀ (n:=2) (abs_nonneg _)
          (abs_vectorFiniteCellGradient_component_global s β t sample.1 i r _ l))
  have hfub:=(bounded_nnreal_interval_fubini Q source hsm a b B hsb).2
  have hmeanm:Measurable (fun r=>∫sample,source r sample∂Q):=
    hsm.stronglyMeasurable.integral_prod_right.measurable
  rw [integral_sub (hig b) (hig a)] at heQ
  rw [hfub,nnreal_intervalIntegral_eq_real _ hmeanm a b hab] at heQ
  simpa only [vectorFixedStateCellSquareMoment,vectorFixedStateCellSourceMean,Real.toNNReal_coe] using heQ

end QuantitativePaper
