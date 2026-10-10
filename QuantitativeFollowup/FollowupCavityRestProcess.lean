module
public import QuantitativeFollowup.AnisotropicSpinMartingale
public import QuantitativeFollowup.FollowupCavityParameters
public import QuantitativeFollowup.ParisiFreeMeasure
public import FourPapersCommon.BoundedOverlapProcessCovariance

@[expose] public section

/-! The genuine rest-system self-overlap process, with its centered
endpoint-fixed L² realization.  Every random variable is evaluated on
the constructed anisotropic diffusion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

def followupCavityRestSpinModel (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) : AnisotropicSpinModel n where
  variance:=fun _=>followupCavityC β ρ
  variance_pos:=fun _=>mul_pos (sq_pos_of_pos hβ) hρ.1
  coupling:=fun e=>if e.1.1=e.1.2 then 0 else followupCavityRestCoupling n β ρ

def cavityRestSelfOverlap (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (ω : AnisotropicDisorderBrownianSample n) : ℝ:=
  anisotropicSelectedMeanSquare Finset.univ (anisotropicProcessMagnetization D μ q ω)

theorem cavityRestSelfOverlap_nonneg (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (ω : AnisotropicDisorderBrownianSample n) :
    0≤cavityRestSelfOverlap D μ q ω := by
  unfold cavityRestSelfOverlap anisotropicSelectedMeanSquare
  positivity

theorem cavityRestSelfOverlap_norm_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (ω : AnisotropicDisorderBrownianSample n) :
    ‖cavityRestSelfOverlap D μ q ω‖≤1 :=
  anisotropicSelectedMeanSquare_bound _ _
    (fun i=>anisotropicMeasureTailMagnetization_component_bound D μ q _ i)

theorem cavityRestSelfOverlap_zero (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (ω : AnisotropicDisorderBrownianSample n) :
    cavityRestSelfOverlap D μ 0 ω=0 := by
  simp [cavityRestSelfOverlap,anisotropicProcessMagnetization_zero,
    anisotropicSelectedMeanSquare]

theorem measurable_uncurry_cavityRestSelfOverlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      cavityRestSelfOverlap D μ z.1 z.2) :=
  (continuous_anisotropicSelectedMeanSquare Finset.univ).measurable.comp
    (measurable_uncurry_anisotropicProcessMagnetization D μ)

def cavityRestOverlapPath (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (ω : AnisotropicDisorderBrownianSample n) : C(Paper.Overlap,ℝ):=
  ⟨fun q=>cavityRestSelfOverlap D μ q ω,
    (continuous_anisotropicSelectedMeanSquare Finset.univ).comp
      (continuous_anisotropicProcessMagnetization_time D μ ω)⟩

theorem measurable_cavityRestOverlapPath (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) : Measurable (cavityRestOverlapPath D μ) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro q
  change Measurable (fun ω : AnisotropicDisorderBrownianSample n=>
    cavityRestSelfOverlap D μ q ω)
  have hi : Measurable (fun ω : AnisotropicDisorderBrownianSample n=>(q,ω)):=
    measurable_const.prodMk measurable_id
  have hh := (measurable_uncurry_cavityRestSelfOverlap D μ).comp hi
  simpa only [Function.comp_def] using hh

theorem cavityRestOverlapPath_norm_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (ω : AnisotropicDisorderBrownianSample n) :
    ‖cavityRestOverlapPath D μ ω‖≤1 := by
  apply ((cavityRestOverlapPath D μ ω).norm_le (by norm_num : (0:ℝ)≤1)).mpr
  intro q
  exact cavityRestSelfOverlap_norm_le D μ q ω

def cavityRestOverlapMean (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) : C(Paper.Overlap,ℝ):=
  overlapProcessMean (anisotropicMeasureSampleLaw D μ a) (cavityRestOverlapPath D μ)

theorem cavityRestOverlapMean_apply (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    cavityRestOverlapMean D μ a q=
      ∫ω,cavityRestSelfOverlap D μ q ω ∂anisotropicMeasureSampleLaw D μ a :=
  overlapProcessMean_apply _ _ (measurable_cavityRestOverlapPath D μ) 1 (by norm_num)
    (cavityRestOverlapPath_norm_le D μ) q

theorem cavityRestOverlapMean_mem_unit (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    cavityRestOverlapMean D μ a q∈Icc (0:ℝ) 1 := by
  constructor
  · rw [cavityRestOverlapMean_apply]
    exact integral_nonneg (cavityRestSelfOverlap_nonneg D μ q)
  · have hh := (cavityRestOverlapMean D μ a).norm_coe_le_norm q
    have hm := overlapProcessMean_norm_le (anisotropicMeasureSampleLaw D μ a)
      (cavityRestOverlapPath D μ) (measurable_cavityRestOverlapPath D μ) 1 (by norm_num)
      (cavityRestOverlapPath_norm_le D μ)
    exact (le_abs_self _).trans (hh.trans hm)

def cavityRestCenteredOverlapPath (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ω : AnisotropicDisorderBrownianSample n) : C(Paper.Overlap,ℝ):=
  overlapCenteredPath (anisotropicMeasureSampleLaw D μ a) (cavityRestOverlapPath D μ) ω

theorem cavityRestCenteredOverlapPath_norm_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ω : AnisotropicDisorderBrownianSample n) :
    ‖cavityRestCenteredOverlapPath D μ a ω‖≤1 := by
  apply ((cavityRestCenteredOverlapPath D μ a ω).norm_le (by norm_num : (0:ℝ)≤1)).mpr
  intro q
  change ‖cavityRestSelfOverlap D μ q ω-cavityRestOverlapMean D μ a q‖≤1
  have hb := cavityRestSelfOverlap_norm_le D μ q ω
  have h0 := cavityRestSelfOverlap_nonneg D μ q ω
  have hm := cavityRestOverlapMean_mem_unit D μ a q
  rw [Real.norm_eq_abs] at hb ⊢
  apply abs_le.mpr
  constructor <;> linarith [hm.1,hm.2,le_abs_self (cavityRestSelfOverlap D μ q ω)]

def cavityRestL2Process (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ω : AnisotropicDisorderBrownianSample n) : Lp ℝ 2 (parisiFreeMeasure μ a):=
  overlapCenteredL2Process (anisotropicMeasureSampleLaw D μ a) (parisiFreeMeasure μ a)
    (cavityRestOverlapPath D μ) ω

def cavityRestEndpointProcess (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ω : AnisotropicDisorderBrownianSample n) :
    endpointFixedL2 (parisiFreeMeasure μ a):=
  overlapCenteredEndpointProcess (anisotropicMeasureSampleLaw D μ a) (parisiFreeMeasure μ a)
    (cavityRestOverlapPath D μ) ω

theorem measurable_cavityRestEndpointProcess (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : Measurable (cavityRestEndpointProcess D μ a):=
  measurable_overlapCenteredEndpointProcess _ _ _ (measurable_cavityRestOverlapPath D μ)

theorem memLp_cavityRestEndpointProcess (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    MemLp (cavityRestEndpointProcess D μ a) 2 (anisotropicMeasureSampleLaw D μ a):=
  memLp_overlapCenteredEndpointProcess _ _ _ (measurable_cavityRestOverlapPath D μ)
    1 (by norm_num) (cavityRestOverlapPath_norm_le D μ)

theorem cavityRestEndpointProcess_coe (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (hone : parisiFreeMeasure μ a {(1:Paper.Overlap)}=0)
    (ω : AnisotropicDisorderBrownianSample n) :
    (cavityRestEndpointProcess D μ a ω : Lp ℝ 2 (parisiFreeMeasure μ a))=
      cavityRestL2Process D μ a ω :=
  overlapCenteredEndpointProcess_coe _ _ _ (measurable_cavityRestOverlapPath D μ)
    1 (by norm_num) (cavityRestOverlapPath_norm_le D μ)
    (cavityRestSelfOverlap_zero D μ) hone ω

end QuantitativeFollowup
