module
public import QuantitativeFollowup.QuantileWindowSupport

@[expose] public section

/-! Atom-sensitive normalized kernels for arbitrary measurable quantile
sets.  These include every nonempty interval, with any choice of endpoints.
The literal restricted quantile pushforward is retained, including partial
atoms; no atom-free or threshold conclusion is assumed. -/
noncomputable section
open Set MeasureTheory Filter Paper
open scoped ENNReal NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def quantileSetMeasure (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ) : Measure Overlap :=
  (volume.restrict I).map (parisiFreeQuantile μ s)

def quantileSetKernel (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ) (x : ℝ)
    (q : Overlap) : ℝ :=
  min 1 (((quantileSetMeasure μ s I).rnDeriv (parisiFreeMeasure μ s) q).toReal)/x

theorem measurable_quantileSetKernel (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ) (x : ℝ) :
    Measurable (quantileSetKernel μ s I x) :=
  (measurable_const.min (Measure.measurable_rnDeriv _ _).ennreal_toReal).div_const _

theorem quantileSetMeasure_le_free (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ)
    (hI : I⊆Ioc (0:ℝ) (1-s)) : quantileSetMeasure μ s I≤parisiFreeMeasure μ s := by
  rw [←parisiFreeQuantile_map μ s]
  apply Measure.map_mono _ (parisiFreeQuantile_measurable μ s)
  exact Measure.restrict_mono_set volume hI

theorem quantileSetKernel_nonneg_le (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ) (x : ℝ)
    (hx : 0<x) (q : Overlap) :
    0≤quantileSetKernel μ s I x q ∧ quantileSetKernel μ s I x q≤1/x :=
  ⟨div_nonneg (le_min zero_le_one ENNReal.toReal_nonneg) hx.le,
    div_le_div_of_nonneg_right (min_le_left _ _) hx.le⟩

theorem quantileSetKernel_eq_rnDeriv (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ) (x : ℝ)
    (hI : I⊆Ioc (0:ℝ) (1-s)) :
    quantileSetKernel μ s I x=ᵐ[parisiFreeMeasure μ s]
      fun q=>((quantileSetMeasure μ s I).rnDeriv (parisiFreeMeasure μ s) q).toReal/x := by
  filter_upwards [Measure.rnDeriv_le_one_of_le (quantileSetMeasure_le_free μ s I hI)] with q hq
  unfold quantileSetKernel
  have hq' : ((quantileSetMeasure μ s I).rnDeriv (parisiFreeMeasure μ s) q).toReal≤1 := by
    change (quantileSetMeasure μ s I).rnDeriv (parisiFreeMeasure μ s) q≤1 at hq
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by norm_num) hq
  rw [min_eq_right hq']

theorem integral_quantileSetKernel_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ) (x : ℝ) (hI : I⊆Ioc (0:ℝ) (1-s))
    (f : Overlap→E) (hf : Measurable f) :
    (∫q,quantileSetKernel μ s I x q • f q ∂parisiFreeMeasure μ s)=
      x⁻¹ • ∫w in I,f (parisiFreeQuantile μ s w) := by
  let :=isFiniteMeasure_of_le (parisiFreeMeasure μ s) (quantileSetMeasure_le_free μ s I hI)
  have hAC:=Measure.absolutelyContinuous_of_le (quantileSetMeasure_le_free μ s I hI)
  calc
    _=∫q,x⁻¹ • (((quantileSetMeasure μ s I).rnDeriv (parisiFreeMeasure μ s) q).toReal • f q)
        ∂parisiFreeMeasure μ s := by
      apply integral_congr_ae
      filter_upwards [quantileSetKernel_eq_rnDeriv μ s I x hI] with q hq
      rw [hq,div_eq_inv_mul,mul_smul]
    _=x⁻¹ • ∫q,f q ∂quantileSetMeasure μ s I := by
      rw [integral_smul,integral_rnDeriv_smul hAC]
    _=_ := by
      rw [quantileSetMeasure,integral_map (parisiFreeQuantile_measurable μ s).aemeasurable
        hf.aestronglyMeasurable]

theorem integral_quantileSetKernel (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ) (x : ℝ)
    (hI : I⊆Ioc (0:ℝ) (1-s)) :
    (∫q,quantileSetKernel μ s I x q ∂parisiFreeMeasure μ s)=volume.real I/x := by
  have h:=integral_quantileSetKernel_smul μ s I x hI (fun _=>(1:ℝ)) measurable_const
  simpa only [smul_eq_mul,mul_one,integral_const,Measure.restrict_apply_univ,Measure.real,
    div_eq_inv_mul] using h

theorem integral_quantileSetKernel_normalized (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ) (x : ℝ)
    (hI : I⊆Ioc (0:ℝ) (1-s)) (hx : 0<x) (hlen : volume.real I=x) :
    (∫q,quantileSetKernel μ s I x q ∂parisiFreeMeasure μ s)=1 := by
  rw [integral_quantileSetKernel μ s I x hI,hlen,div_self hx.ne']

theorem memLp_quantileSetKernel (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ) (x : ℝ) (hx : 0<x) :
    MemLp (quantileSetKernel μ s I x) 2 (parisiFreeMeasure μ s) := by
  exact MemLp.of_bound (measurable_quantileSetKernel μ s I x).aestronglyMeasurable (1/x)
    (.of_forall fun q=>by
      rw [Real.norm_of_nonneg (quantileSetKernel_nonneg_le μ s I x hx q).1]
      exact (quantileSetKernel_nonneg_le μ s I x hx q).2)

theorem ae_quantileSetKernel_property (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ) (x : ℝ)
    (hI : I⊆Ioc (0:ℝ) (1-s)) (p : Overlap→Prop) (hp : MeasurableSet {q | p q})
    (h : ∀ᵐw ∂volume.restrict I,p (parisiFreeQuantile μ s w)) :
    ∀ᵐq ∂parisiFreeMeasure μ s,quantileSetKernel μ s I x q≠0→p q := by
  let :=isFiniteMeasure_of_le (parisiFreeMeasure μ s) (quantileSetMeasure_le_free μ s I hI)
  have hw : ∀ᵐq ∂quantileSetMeasure μ s I,p q :=
    (ae_map_iff (parisiFreeQuantile_measurable μ s).aemeasurable hp).mpr h
  filter_upwards [Measure.ae_rnDeriv_ne_zero_imp_of_ae (parisiFreeMeasure μ s) hw] with q hq hκ
  apply hq
  intro hz
  apply hκ
  simp only [quantileSetKernel,hz,ENNReal.toReal_zero,min_eq_right zero_le_one,zero_div]

theorem ae_quantileSetKernel_future (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ) (x : ℝ)
    (hI : I⊆Ioc (0:ℝ) (1-s)) (q : Overlap)
    (h : ∀ᵐw ∂volume.restrict I,q≤parisiFreeQuantile μ s w) :
    ∀ᵐp ∂parisiFreeMeasure μ s,quantileSetKernel μ s I x p≠0→q≤p :=
  ae_quantileSetKernel_property μ s I x hI (fun p=>q≤p) measurableSet_Ici h

theorem ae_quantileSetKernel_past (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ) (x : ℝ)
    (hI : I⊆Ioc (0:ℝ) (1-s)) (q : Overlap)
    (h : ∀ᵐw ∂volume.restrict I,parisiFreeQuantile μ s w≤q) :
    ∀ᵐp ∂parisiFreeMeasure μ s,quantileSetKernel μ s I x p≠0→p≤q :=
  ae_quantileSetKernel_property μ s I x hI (fun p=>p≤q) measurableSet_Iic h

theorem ae_quantileSetKernel_threshold (μ : ParisiMeasure) (s : ℝ) (I : Set ℝ) (x u : ℝ)
    (hI : I⊆Ioc (0:ℝ) (1-s))
    (h : ∀ᵐw ∂volume.restrict I,u≤parisiCDF μ (parisiFreeQuantile μ s w)) :
    ∀ᵐp ∂parisiFreeMeasure μ s,quantileSetKernel μ s I x p≠0→u≤parisiCDF μ p :=
  ae_quantileSetKernel_property μ s I x hI (fun p=>u≤parisiCDF μ p)
    (measurableSet_le measurable_const ((parisiCDF_measurable μ).comp measurable_subtype_coe)) h

end QuantitativeFollowup
