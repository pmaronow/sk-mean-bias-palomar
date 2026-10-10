module
public import QuantitativeFollowup.QuantileWindowSupport

@[expose] public section

/-! The literal padded quantile window.  Its averaging law is an actual
probability measure, and observables vanishing at the root agree exactly
with the Radon--Nikodym Stieltjes kernel. -/
noncomputable section
open Set MeasureTheory Filter Paper
open scoped Topology ENNReal NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def parisiPaddedFreeQuantile (μ : ParisiMeasure) (s w : ℝ) : Overlap :=
  if w≤0 then QuantitativePaper.zeroOverlap else parisiFreeQuantile μ s w

theorem measurable_parisiPaddedFreeQuantile (μ : ParisiMeasure) (s : ℝ) :
    Measurable (parisiPaddedFreeQuantile μ s) :=
  Measurable.ite measurableSet_Iic measurable_const (parisiFreeQuantile_measurable μ s)

theorem parisiPaddedFreeQuantile_monotone (μ : ParisiMeasure) (s : ℝ) :
    Monotone (parisiPaddedFreeQuantile μ s) := by
  intro w z hwz
  unfold parisiPaddedFreeQuantile
  by_cases hz : z≤0
  · rw [ite_eq_left hz,ite_eq_left (hwz.trans hz)]
  · rw [ite_eq_right hz]
    by_cases hw : w≤0
    · rw [ite_eq_left hw]
      exact (parisiFreeQuantile μ s z).property.1
    · rw [ite_eq_right hw]
      exact parisiFreeQuantile_monotone μ s hwz

def quantileWindowAveraging (v x : ℝ) : Measure ℝ :=
  ENNReal.ofReal x⁻¹ • volume.restrict (Ioc (v-x) v)

instance quantileWindowAveraging_finite (v x : ℝ) : IsFiniteMeasure (quantileWindowAveraging v x) := by
  constructor
  simp only [quantileWindowAveraging,Measure.smul_apply,Measure.restrict_apply_univ,Real.volume_Ioc,smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem quantileWindowAveraging_probability (v x : ℝ) (hx : 0<x) :
    IsProbabilityMeasure (quantileWindowAveraging v x) := by
  constructor
  simp only [quantileWindowAveraging,Measure.smul_apply,Measure.restrict_apply_univ,
    Real.volume_Ioc,smul_eq_mul]
  rw [show v-(v-x)=x by ring,ENNReal.ofReal_inv_of_pos hx]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hx)) ENNReal.ofReal_ne_top

theorem integral_quantileWindowAveraging_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v x : ℝ) (hx : 0<x) (f : ℝ→E) :
    (∫w,f w ∂quantileWindowAveraging v x)=x⁻¹ • ∫w in Ioc (v-x) v,f w := by
  rw [quantileWindowAveraging,integral_smul_measure,ENNReal.toReal_ofReal (inv_nonneg.mpr hx.le)]

theorem integral_padded_window_eq_positive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : ParisiMeasure) (s v x : ℝ) (f : Overlap→E) (hf0 : f QuantitativePaper.zeroOverlap=0) :
    (∫w in Ioc (v-x) v,f (parisiPaddedFreeQuantile μ s w))=
      ∫w in Ioc (max 0 (v-x)) v,f (parisiFreeQuantile μ s w) := by
  have hfun : (fun w=>f (parisiPaddedFreeQuantile μ s w))=
      (Ioi (0:ℝ)).indicator (fun w=>f (parisiFreeQuantile μ s w)) := by
    funext w
    by_cases hw : w≤0
    · simp only [parisiPaddedFreeQuantile,ite_eq_left hw,hf0]
      rw [indicator_of_notMem (show w∉Ioi (0:ℝ) from not_lt.mpr hw)]
    · simp only [parisiPaddedFreeQuantile,ite_eq_right hw]
      rw [indicator_of_mem (show w∈Ioi (0:ℝ) from lt_of_not_ge hw)]
  rw [hfun,integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi (0:ℝ)∩Ioc (v-x) v=Ioc (max 0 (v-x)) v := by
    ext w
    simp only [mem_inter_iff,mem_Ioi,mem_Ioc,max_lt_iff]
    tauto
  rw [hset]

theorem integral_padded_window_eq_kernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ParisiMeasure) (s v x : ℝ) (hv : v≤1-s) (hx : 0<x)
    (f : Overlap→E) (hf : Measurable f) (hf0 : f QuantitativePaper.zeroOverlap=0) :
    (∫w,f (parisiPaddedFreeQuantile μ s w) ∂quantileWindowAveraging v x)=
      ∫q,quantileWindowKernel μ s v x q • f q ∂parisiFreeMeasure μ s := by
  rw [integral_quantileWindowAveraging_smul v x hx,
    integral_padded_window_eq_positive μ s v x f hf0,
    integral_quantileWindowKernel_smul μ s v x hv f hf]

end QuantitativeFollowup
