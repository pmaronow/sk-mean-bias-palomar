module
public import QuantitativeFollowup.VectorQuantileSetVariance

@[expose] public section

/-! Genuine deterministic mean-level bounds for normalized nonnegative
kernels, transferred from an almost-everywhere quantile range. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000

theorem integrable_kernel_level (μ : Paper.ParisiMeasure) (s : ℝ)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hiκ : Integrable κ (parisiFreeMeasure μ s)) :
    Integrable (fun p=>κ p*(p:ℝ)) (parisiFreeMeasure μ s) := by
  apply hiκ.norm.mono' (hκ.mul measurable_subtype_coe).aestronglyMeasurable
  exact .of_forall fun p=>by
    change ‖κ p*(p:ℝ)‖≤‖κ p‖
    rw [norm_mul,Real.norm_of_nonneg p.property.1]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left p.property.2 (norm_nonneg _)

theorem vectorKernelOverlapLevel_bounds (μ : Paper.ParisiMeasure) (s : ℝ)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hiκ : Integrable κ (parisiFreeMeasure μ s))
    (hκpos : ∀p,0≤κ p) (hnormal : (∫p,κ p ∂parisiFreeMeasure μ s)=1)
    (u v : ℝ) (hSupport : ∀ᵐp ∂parisiFreeMeasure μ s,κ p≠0→(p:ℝ)∈Icc u v) :
    u≤vectorKernelOverlapLevel μ s κ ∧ vectorKernelOverlapLevel μ s κ≤v := by
  have hi:=integrable_kernel_level μ s κ hκ hiκ
  have hl : (fun p=>κ p*u)≤ᵐ[parisiFreeMeasure μ s]fun p=>κ p*(p:ℝ) := by
    filter_upwards [hSupport] with p hp
    by_cases hz : κ p=0
    · simp only [hz,zero_mul,le_refl]
    · exact mul_le_mul_of_nonneg_left (hp hz).1 (hκpos p)
  have hr : (fun p=>κ p*(p:ℝ))≤ᵐ[parisiFreeMeasure μ s]fun p=>κ p*v := by
    filter_upwards [hSupport] with p hp
    by_cases hz : κ p=0
    · simp only [hz,zero_mul,le_refl]
    · exact mul_le_mul_of_nonneg_left (hp hz).2 (hκpos p)
  have hl':=integral_mono_ae (hiκ.mul_const u) hi hl
  have hr':=integral_mono_ae hi (hiκ.mul_const v) hr
  constructor
  · simpa only [vectorKernelOverlapLevel,integral_mul_const,hnormal,one_mul] using hl'
  · simpa only [vectorKernelOverlapLevel,integral_mul_const,hnormal,one_mul] using hr'

theorem vectorKernelOverlapLevel_quantileSet_bounds (μ : Paper.ParisiMeasure) (s : ℝ)
    (I : Set ℝ) (x : ℝ) (hI : I⊆Ioc (0:ℝ) (1-s)) (hx : 0<x) (hlen : volume.real I=x)
    (u v : ℝ) (hRange : ∀ᵐw ∂volume.restrict I,(parisiFreeQuantile μ s w:ℝ)∈Icc u v) :
    u≤vectorKernelOverlapLevel μ s (quantileSetKernel μ s I x) ∧
      vectorKernelOverlapLevel μ s (quantileSetKernel μ s I x)≤v := by
  apply vectorKernelOverlapLevel_bounds μ s _ (measurable_quantileSetKernel μ s I x)
    ((memLp_quantileSetKernel μ s I x hx).integrable one_le_two)
    (fun p=>(quantileSetKernel_nonneg_le μ s I x hx p).1)
    (integral_quantileSetKernel_normalized μ s I x hI hx hlen)
  exact ae_quantileSetKernel_property μ s I x hI (fun p=>(p:ℝ)∈Icc u v)
    (measurable_subtype_coe measurableSet_Icc) hRange

end QuantitativeFollowup
