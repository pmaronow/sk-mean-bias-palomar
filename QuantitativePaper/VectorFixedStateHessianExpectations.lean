module
public import QuantitativePaper.VectorFixedStateHessianSourceBounds
public import QuantitativePaper.VectorTiltedIntegral
public import FourPapersCommon.BoundedTimeInterval
public import FourPapersCommon.LocalItoEndpoints

@[expose] public section

/-! Actual fractional-tilt expectations of finite Hessians and their true
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

def vectorFixedStateCellHessianMean (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (r : ℝ) : ℝ :=
  ∫sample,vectorFiniteCellHessianDiagonal s β t sample.1 i r.toNNReal
    (vectorMeasureState μ β t ht r.toNNReal sample) l∂vectorMeasureDisorderTilt μ β t outer

def vectorFixedStateCellHessianSourceMean (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (r : ℝ) : ℝ :=
  ∫sample,vectorFixedStateCellHessianSource s μ β t ht i r.toNNReal sample l
    ∂vectorMeasureDisorderTilt μ β t outer

theorem continuous_vectorFixedStateCellHessianMean (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1) (l : Fin n) :
    Continuous (vectorFixedStateCellHessianMean s μ β t outer ht i l) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t outer ht
  apply continuous_of_dominated (μ:=vectorMeasureDisorderTilt μ β t outer) (bound:=fun _=>(2:ℝ))
  · intro r
    exact (measurable_vectorFixedStateCellHessian s μ β t ht i l r.toNNReal).aestronglyMeasurable
  · intro r
    exact .of_forall fun sample=>by
      rw [Real.norm_eq_abs]
      exact abs_vectorFiniteCellHessianDiagonal_global s β t sample.1 i hi _ _ l
  · exact integrable_const _
  · exact .of_forall fun sample=>(continuous_vectorFixedStateCellHessian_path s μ β t ht i l sample).comp
      continuous_real_toNNReal

theorem vectorFixedStateCellHessianSourceMean_intervalIntegrable (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1) (l : Fin n) (a b : ℝ) :
    IntervalIntegrable (vectorFixedStateCellHessianSourceMean s μ β t outer ht i l) volume a b := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t outer ht
  let source:ℝ→VectorDisorderBrownianSample n→ℝ:=fun r sample=>
    vectorFixedStateCellHessianSource s μ β t ht i r.toNNReal sample l
  have hmap:Measurable (fun z : ℝ×VectorDisorderBrownianSample n=>(z.1.toNNReal,z.2)):=
    measurable_real_toNNReal.prodMap measurable_id
  have hm:=(measurable_uncurry_vectorFixedStateCellHessianSource s μ β t ht i l).comp hmap
  dsimp only [Function.comp_def] at hm
  have hmeanm:Measurable (fun r : ℝ=>∫sample,source r sample∂vectorMeasureDisorderTilt μ β t outer):=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  let B:ℝ:=((1-t)*β^2)*(2*vectorFiniteCellHessianDerivativeBound s β t i l*Real.sqrt n+
      (n:ℝ)*(vectorFiniteCellGradientDerivativeBound s β t i l:ℝ)^2)
  apply (intervalIntegrable_const (c:=B)).mono_fun' hmeanm.aestronglyMeasurable
  exact .of_forall fun r=>by
    change ‖∫sample,source r sample∂vectorMeasureDisorderTilt μ β t outer‖≤B
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=vectorMeasureDisorderTilt (n:=n) μ β t outer)
      (.of_forall (norm_vectorFixedStateCellHessianSource_le s μ β t ht i hi l r.toNNReal))

theorem vectorFixedState_hessian_tilted_cropped (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1) (l : Fin n)
    (a b : ℝ≥0) (hab : a≤b) (hb : (b:ℝ)<s.q (i+1)) :
    vectorFixedStateCellHessianMean s μ β t outer ht.le i l b-
      vectorFixedStateCellHessianMean s μ β t outer ht.le i l a=
      ∫r in (a:ℝ)..(b:ℝ),vectorFixedStateCellHessianSourceMean s μ β t outer ht.le i l r := by
  let P:=vectorDisorderBrownianMeasure n
  let Q:=vectorMeasureDisorderTilt (n:=n) μ β t outer
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t outer ht.le
  let g:ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>
    vectorFiniteCellHessianDiagonal s β t sample.1 i r (vectorMeasureState μ β t ht.le r sample) l
  let source:ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>
    vectorFixedStateCellHessianSource s μ β t ht.le i r sample l
  let B:ℝ:=((1-t)*β^2)*(2*vectorFiniteCellHessianDerivativeBound s β t i l*Real.sqrt n+
    (n:ℝ)*(vectorFiniteCellGradientDerivativeBound s β t i l:ℝ)^2)
  have hsb:∀r sample,‖source r sample‖≤B:=norm_vectorFixedStateCellHessianSource_le s μ β t ht.le i hi l
  have hsm:Measurable (Function.uncurry source):=measurable_uncurry_vectorFixedStateCellHessianSource s μ β t ht.le i l
  let F:=fun sample=>g b sample-g a sample
  let H:=fun sample=>∫r in Ioc a b,source r sample∂nonnegativeLebesgueMeasure
  let W:=fun sample : VectorDisorderBrownianSample n=>Real.exp (outer*vectorMeasurePotential μ β t sample.1 0)
  have hWpast:Measurable[vectorBrownianFiltration n 0] W:=
    (Real.measurable_exp.comp (measurable_const.mul (measurable_vectorMeasurePotential_initial μ β t ht.le))).comp
      (stronglyMeasurable_initialVectorDisorder n 0).measurable
  have hWm:Measurable W:=hWpast.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hWn:∀sample,0≤W sample:=fun _=>(Real.exp_pos _).le
  have hWi:Integrable W P:=(integrable_exp_vectorMeasurePotential μ β t ht.le outer (0:Field n)).comp_fst (vectorBrownianMeasure n)
  have hFm:Measurable F:=(measurable_vectorFixedStateCellHessian s μ β t ht.le i l b).sub
    (measurable_vectorFixedStateCellHessian s μ β t ht.le i l a)
  have hFb:∀sample,‖F sample‖≤4:=fun sample=>by
    have ha:=abs_vectorFiniteCellHessianDiagonal_global s β t sample.1 i hi a
      (vectorMeasureState μ β t ht.le a sample) l
    have hb:=abs_vectorFiniteCellHessianDiagonal_global s β t sample.1 i hi b
      (vectorMeasureState μ β t ht.le b sample) l
    dsimp only [F,g]
    exact (norm_sub_le _ _).trans (by simpa only [Real.norm_eq_abs,show (2 : ℝ)+2=4 by norm_num] using add_le_add hb ha)
  have hHm:Measurable H:=measurable_nnreal_intervalIntegral source hsm a b
  have hHb:∀sample,‖H sample‖≤B*max ((b:ℝ)-a) 0:=norm_nnreal_intervalIntegral_le source a b B hsb
  have he:(∫sample,W sample*F sample∂P)=∫sample,W sample*H sample∂P := by
    apply integral_eq_of_truncated_weight_identity P F H W hFm hHm 4 (B*max ((b:ℝ)-a) 0) hFb hHb hWm hWn hWi
    intro j
    have hZ:Measurable[vectorBrownianFiltration n 0] (truncateWeight W j):=
      measurable_const.min hWpast
    have hh:=(vectorFixedState_hessian_cropped s μ β t hβ ht i l a b hab hb
      (truncateWeight W j) hZ (j:ℝ≥0)
      (norm_truncateWeight_le W hWn j)).2
    simp only [integral_const_mul] at hh
    exact hh
  have heQ:(∫sample,F sample∂Q)=∫sample,H sample∂Q:=by
    rw [integral_vectorMeasureDisorderTilt μ β t outer ht.le,
      integral_vectorMeasureDisorderTilt μ β t outer ht.le]
    exact congrArg (fun x=>x/vectorMeasureOuterPartition (n:=n) μ β t outer) he
  have hig (r : ℝ≥0) : Integrable (fun sample=>g r sample) Q:=
    (integrable_const (2:ℝ)).mono'
      (measurable_vectorFixedStateCellHessian s μ β t ht.le i l r).aestronglyMeasurable
      (.of_forall fun sample=>by
        rw [Real.norm_eq_abs]
        exact abs_vectorFiniteCellHessianDiagonal_global s β t sample.1 i hi r _ l)
  have hfub:=(bounded_nnreal_interval_fubini Q source hsm a b B hsb).2
  have hmeanm:Measurable (fun r=>∫sample,source r sample∂Q):=
    hsm.stronglyMeasurable.integral_prod_right.measurable
  rw [integral_sub (hig b) (hig a)] at heQ
  rw [hfub,nnreal_intervalIntegral_eq_real _ hmeanm a b hab] at heQ
  simpa only [vectorFixedStateCellHessianMean,vectorFixedStateCellHessianSourceMean,Real.toNNReal_coe] using heQ

end QuantitativePaper
