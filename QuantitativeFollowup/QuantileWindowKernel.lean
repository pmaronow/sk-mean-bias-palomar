module
public import QuantitativeFollowup.ParisiFreeQuantile
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

/-! The actual Radon--Nikodym kernel of a quantile window, retaining
partial atoms.  Its density is capped only on a null set and gives exact
Stieltjes integral pairings. -/
noncomputable section
open Set MeasureTheory Filter Paper
open scoped ENNReal NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def quantileWindowMeasure (μ : ParisiMeasure) (s v x : ℝ) : Measure Overlap :=
  (volume.restrict (Ioc (max 0 (v-x)) v)).map (parisiFreeQuantile μ s)

theorem quantileWindowMeasure_univ (μ : ParisiMeasure) (s v x : ℝ) :
    quantileWindowMeasure μ s v x univ=ENNReal.ofReal (v-max 0 (v-x)) := by
  rw [quantileWindowMeasure,Measure.map_apply (parisiFreeQuantile_measurable μ s) .univ]
  simp only [preimage_univ,Measure.restrict_apply_univ,Real.volume_Ioc]

instance quantileWindowMeasure_finite (μ : ParisiMeasure) (s v x : ℝ) :
    IsFiniteMeasure (quantileWindowMeasure μ s v x) :=
  ⟨by rw [quantileWindowMeasure_univ];exact ENNReal.ofReal_lt_top⟩

theorem quantileWindowMeasure_le_free (μ : ParisiMeasure) (s v x : ℝ)
    (hv : v≤1-s) : quantileWindowMeasure μ s v x≤parisiFreeMeasure μ s := by
  rw [←parisiFreeQuantile_map μ s]
  apply Measure.map_mono _ (parisiFreeQuantile_measurable μ s)
  exact Measure.restrict_mono_set volume fun w hw=>
    ⟨(le_max_left 0 (v-x)).trans_lt hw.1,hw.2.trans hv⟩

def quantileWindowKernel (μ : ParisiMeasure) (s v x : ℝ) (q : Overlap) : ℝ :=
  min 1 (((quantileWindowMeasure μ s v x).rnDeriv (parisiFreeMeasure μ s) q).toReal)/x

theorem measurable_quantileWindowKernel (μ : ParisiMeasure) (s v x : ℝ) :
    Measurable (quantileWindowKernel μ s v x) :=
  (measurable_const.min (Measure.measurable_rnDeriv _ _).ennreal_toReal).div_const _

theorem quantileWindowKernel_nonneg_le (μ : ParisiMeasure) (s v x : ℝ) (hx : 0<x)
    (q : Overlap) : 0≤quantileWindowKernel μ s v x q ∧ quantileWindowKernel μ s v x q≤1/x := by
  exact ⟨div_nonneg (le_min (by norm_num) ENNReal.toReal_nonneg) hx.le,
    div_le_div_of_nonneg_right (min_le_left _ _) hx.le⟩

theorem quantileWindowKernel_eq_rnDeriv (μ : ParisiMeasure) (s v x : ℝ) (hv : v≤1-s) :
    quantileWindowKernel μ s v x=ᵐ[parisiFreeMeasure μ s]
      fun q=>((quantileWindowMeasure μ s v x).rnDeriv (parisiFreeMeasure μ s) q).toReal/x := by
  filter_upwards [Measure.rnDeriv_le_one_of_le (quantileWindowMeasure_le_free μ s v x hv)] with q hq
  unfold quantileWindowKernel
  have hq' : ((quantileWindowMeasure μ s v x).rnDeriv (parisiFreeMeasure μ s) q).toReal≤1 := by
    change (quantileWindowMeasure μ s v x).rnDeriv (parisiFreeMeasure μ s) q≤1 at hq
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by norm_num) hq
  rw [min_eq_right hq']

theorem integral_quantileWindowKernel_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ParisiMeasure) (s v x : ℝ) (hv : v≤1-s) (f : Overlap→E) (hf : Measurable f) :
    (∫q,quantileWindowKernel μ s v x q • f q ∂parisiFreeMeasure μ s)=
      x⁻¹ • ∫w in Ioc (max 0 (v-x)) v,f (parisiFreeQuantile μ s w) := by
  have hAC:=Measure.absolutelyContinuous_of_le (quantileWindowMeasure_le_free μ s v x hv)
  calc
    _=∫q,x⁻¹ • (((quantileWindowMeasure μ s v x).rnDeriv (parisiFreeMeasure μ s) q).toReal • f q)
      ∂parisiFreeMeasure μ s := by
      apply integral_congr_ae
      filter_upwards [quantileWindowKernel_eq_rnDeriv μ s v x hv] with q hq
      rw [hq,div_eq_inv_mul,mul_smul]
    _=x⁻¹ • ∫q,f q ∂quantileWindowMeasure μ s v x := by
      rw [integral_smul,integral_rnDeriv_smul hAC]
    _=_ := by
      rw [quantileWindowMeasure,integral_map (parisiFreeQuantile_measurable μ s).aemeasurable
        hf.aestronglyMeasurable]

theorem integral_quantileWindowKernel (μ : ParisiMeasure) (s v x : ℝ) (hv : v≤1-s) :
    (∫q,quantileWindowKernel μ s v x q ∂parisiFreeMeasure μ s)=
      max (v-max 0 (v-x)) 0/x := by
  have h:=integral_quantileWindowKernel_smul μ s v x hv (fun _=>(1 : ℝ)) measurable_const
  simp only [smul_eq_mul,mul_one,integral_const,Measure.restrict_apply_univ,Real.volume_Ioc,
    Measure.real,ENNReal.toReal_ofReal'] at h
  simpa only [div_eq_inv_mul] using h

end QuantitativeFollowup
