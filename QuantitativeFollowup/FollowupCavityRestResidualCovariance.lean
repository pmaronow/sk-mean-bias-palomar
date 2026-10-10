module
public import QuantitativeFollowup.FollowupCavityRestFutureSquare
public import QuantitativeFollowup.ScalarFutureContinuity
public import FourPapersCommon.BoundedProductKernelSquare

@[expose] public section

/-! The scalar and rest residual kernels in the actual penalty. The rest
residual subtracts the genuine full-past conditional mean; the scalar
kernel is the genuine restarted square expectation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper Paper FRSB
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityScalarFutureSquare (β : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) (ω : Paper.BrownianSample) : ℝ :=
  scalarFutureSquareExtended β μ r p (parisiPhysicalSplitState β 0 μ r ω)

theorem measurable_cavityScalarFutureSquare (β : ℝ) (μ : Paper.ParisiMeasure) :
    Measurable (fun z : (Paper.Overlap×Paper.Overlap)×Paper.BrownianSample=>
      cavityScalarFutureSquare β μ z.1.1 z.1.2 z.2) := by
  change Measurable (fun z : (Paper.Overlap×Paper.Overlap)×Paper.BrownianSample=>
    scalarFutureSquareExtended β μ z.1.1 z.1.2 (parisiPhysicalSplitState β 0 μ z.1.1 z.2))
  have hpath : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×Paper.BrownianSample=>
      parisiNoiseStatePath β 0 μ (canonicalBrownianPath z.2)) := (measurable_parisiNoiseStatePath β 0 μ).comp
    (measurable_canonicalBrownianPath.comp (measurable_snd : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×Paper.BrownianSample=>z.2)))
  have hx : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×Paper.BrownianSample=>
      parisiPhysicalSplitState β 0 μ z.1.1 z.2) := by
    have he := continuous_eval.measurable.comp (hpath.prodMk measurable_fst.fst)
    simpa only [parisiPhysicalSplitState,Function.comp_def] using he
  have hc : Continuous (fun z : Paper.Overlap×(Paper.Overlap×ℝ)=>
      scalarFutureSquareExtended β μ z.1 z.2.1 z.2.2) := by
    convert! (continuous_scalarFutureSquareExtended β).comp
      (continuous_const.prodMk continuous_id) using 1
  have hg := hc.measurable.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk hx))
  exact hg

theorem cavityScalarFutureSquare_mem_unit (β : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) (ω : Paper.BrownianSample) :
    cavityScalarFutureSquare β μ r p ω∈Icc (0:ℝ) 1 := by
  refine ⟨integral_nonneg fun _=>sq_nonneg _,?_⟩
  have hb (W : C(Paper.Overlap,ℝ)) :
      ‖parisiGradient β μ (p,scalarFutureEndpointExtended β μ r p
        (parisiPhysicalSplitState β 0 μ r ω) W)^2‖≤(1:ℝ) := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_parisiGradient_le_one β μ _)
  have hh := norm_integral_le_of_norm_le_const (μ:=canonicalWienerMeasure) (.of_forall hb)
  exact (le_abs_self _).trans (by
    simpa only [cavityScalarFutureSquare,scalarFutureSquareExtended,
      Real.norm_eq_abs,probReal_univ,mul_one] using hh)

def cavityScalarFutureMean (β : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) : ℝ :=
  ∫ω,cavityScalarFutureSquare β μ r p ω ∂canonicalBrownianMeasure

theorem measurable_cavityScalarFutureMean (β : ℝ) (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×Paper.Overlap=>cavityScalarFutureMean β μ z.1 z.2) :=
  (measurable_cavityScalarFutureSquare β μ).stronglyMeasurable.integral_prod_right'.measurable

theorem cavityScalarFutureMean_mem_unit (β : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) : cavityScalarFutureMean β μ r p∈Icc (0:ℝ) 1 := by
  refine ⟨integral_nonneg fun ω=>(cavityScalarFutureSquare_mem_unit β μ r p ω).1,?_⟩
  have hb (ω : Paper.BrownianSample) : ‖cavityScalarFutureSquare β μ r p ω‖≤(1:ℝ) := by
    rw [Real.norm_of_nonneg (cavityScalarFutureSquare_mem_unit β μ r p ω).1]
    exact (cavityScalarFutureSquare_mem_unit β μ r p ω).2
  have hh := norm_integral_le_of_norm_le_const (μ:=canonicalBrownianMeasure) (.of_forall hb)
  exact (le_abs_self _).trans (by
    simpa only [cavityScalarFutureMean,Real.norm_eq_abs,probReal_univ,mul_one] using hh)

theorem cavityScalarFutureMean_eq_gamma (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (r p : Paper.Overlap) (hrp : r≤p) :
    cavityScalarFutureMean β μ r p=Gamma β μ p := by
  unfold cavityScalarFutureMean cavityScalarFutureSquare
  simp only [scalarFutureSquareExtended_eq β μ r p hrp]
  exact integral_scalarFutureSquareProcess β hβ μ r p hrp

def cavityScalarFutureCenteredTail (β : ℝ) (μ : Paper.ParisiMeasure)
    (r : Paper.Overlap) (z : Paper.BrownianSample×Paper.Overlap) : ℝ :=
  if r<z.2 then cavityScalarFutureSquare β μ r z.2 z.1-cavityScalarFutureMean β μ r z.2 else 0

def cavityRestFutureResidualTail (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (r : Paper.Overlap) (z : AnisotropicDisorderBrownianSample n×Paper.Overlap) : ℝ :=
  if r<z.2 then cavityRestSelfOverlap D μ z.2 z.1-cavityRestFutureSquare D μ r z.2 z.1 else 0

theorem measurable_cavityScalarFutureCenteredTail (β : ℝ) (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×(Paper.BrownianSample×Paper.Overlap)=>
      cavityScalarFutureCenteredTail β μ z.1 z.2) := by
  have hm : Measurable (fun z : Paper.Overlap×(Paper.BrownianSample×Paper.Overlap)=>
      cavityScalarFutureSquare β μ z.1 z.2.2 z.2.1) := by
    convert! (measurable_cavityScalarFutureSquare β μ).comp
      ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst) using 1
  have hh : Measurable (fun z : Paper.Overlap×(Paper.BrownianSample×Paper.Overlap)=>
      cavityScalarFutureMean β μ z.1 z.2.2) := (measurable_cavityScalarFutureMean β μ).comp
    (measurable_fst.prodMk measurable_snd.snd)
  change Measurable (fun z : Paper.Overlap×(Paper.BrownianSample×Paper.Overlap)=>
    if z.1<z.2.2 then cavityScalarFutureSquare β μ z.1 z.2.2 z.2.1-cavityScalarFutureMean β μ z.1 z.2.2 else 0)
  exact (hm.sub hh).ite (measurableSet_lt measurable_fst measurable_snd.snd) measurable_const

theorem measurable_cavityRestFutureResidualTail (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Paper.Overlap)=>
      cavityRestFutureResidualTail D μ z.1 z.2) := by
  have hm : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Paper.Overlap)=>
      cavityRestSelfOverlap D μ z.2.2 z.2.1) := by
    convert! (measurable_uncurry_cavityRestSelfOverlap D μ).comp
      (measurable_snd.snd.prodMk measurable_snd.fst) using 1
  have hh : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Paper.Overlap)=>
      cavityRestFutureSquare D μ z.1 z.2.2 z.2.1) := by
    convert! (measurable_cavityRestFutureSquare D μ).comp
      (measurable_fst.prodMk (measurable_snd.snd.prodMk measurable_snd.fst)) using 1
  change Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Paper.Overlap)=>
    if z.1<z.2.2 then cavityRestSelfOverlap D μ z.2.2 z.2.1-cavityRestFutureSquare D μ z.1 z.2.2 z.2.1 else 0)
  exact (hm.sub hh).ite (measurableSet_lt measurable_fst measurable_snd.snd) measurable_const

theorem cavityScalarFutureCenteredTail_norm_le (β : ℝ) (μ : Paper.ParisiMeasure)
    (r : Paper.Overlap) (z : Paper.BrownianSample×Paper.Overlap) :
    ‖cavityScalarFutureCenteredTail β μ r z‖≤1 := by
  unfold cavityScalarFutureCenteredTail
  split_ifs
  · have h1 := cavityScalarFutureSquare_mem_unit β μ r z.2 z.1
    have h2 := cavityScalarFutureMean_mem_unit β μ r z.2
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
  · simp

theorem cavityRestFutureResidualTail_norm_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r : Paper.Overlap)
    (z : AnisotropicDisorderBrownianSample n×Paper.Overlap) :
    ‖cavityRestFutureResidualTail D μ r z‖≤1 := by
  unfold cavityRestFutureResidualTail
  split_ifs
  · have h1 := cavityRestSelfOverlap_nonneg D μ z.2 z.1
    have h2 := cavityRestSelfOverlap_norm_le D μ z.2 z.1
    have h3 := cavityRestFutureSquare_mem_unit D μ r z.2 z.1
    rw [Real.norm_of_nonneg h1] at h2
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith [h3.1,h3.2]
  · simp

def cavityScalarFutureCovariance (β : ℝ) (μ : Paper.ParisiMeasure)
    (r p l : Paper.Overlap) : ℝ :=
  ∫ω,cavityScalarFutureCenteredTail β μ r (ω,p)*
    cavityScalarFutureCenteredTail β μ r (ω,l) ∂canonicalBrownianMeasure

def cavityRestResidualCovariance (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (r p l : Paper.Overlap) : ℝ :=
  ∫ω,cavityRestFutureResidualTail D μ r (ω,p)*
    cavityRestFutureResidualTail D μ r (ω,l) ∂anisotropicMeasureSampleLaw D μ a

theorem cavityScalarFutureCovariance_eq_covariance (β : ℝ) (μ : Paper.ParisiMeasure)
    (r p l : Paper.Overlap) (hrp : r<p) (hrl : r<l) :
    cavityScalarFutureCovariance β μ r p l=
      covariance (cavityScalarFutureSquare β μ r p) (cavityScalarFutureSquare β μ r l)
        canonicalBrownianMeasure := by
  simp only [cavityScalarFutureCovariance,cavityScalarFutureCenteredTail,if_pos hrp,if_pos hrl,
    covariance,cavityScalarFutureMean]

theorem cavityRestResidualCovariance_eq_fullPast (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p l : Paper.Overlap) (hrp : r<p) (hrl : r<l) :
    cavityRestResidualCovariance D μ a r p l=
      ∫ω,(cavityRestSelfOverlap D μ p ω-(anisotropicMeasureSampleLaw D μ a)[cavityRestSelfOverlap D μ p|
          anisotropicBrownianFiltration n (r:ℝ).toNNReal] ω)*
        (cavityRestSelfOverlap D μ l ω-(anisotropicMeasureSampleLaw D μ a)[cavityRestSelfOverlap D μ l|
          anisotropicBrownianFiltration n (r:ℝ).toNNReal] ω) ∂anisotropicMeasureSampleLaw D μ a := by
  apply integral_congr_ae
  filter_upwards [cavityRestFutureSquare_condExp D μ a r p hrp.le,
    cavityRestFutureSquare_condExp D μ a r l hrl.le] with ω hp hl
  simp only [cavityRestFutureResidualTail,if_pos hrp,if_pos hrl]
  rw [hp,hl]

end QuantitativeFollowup
