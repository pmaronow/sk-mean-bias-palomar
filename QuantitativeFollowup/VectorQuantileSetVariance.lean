module
public import QuantitativeFollowup.QuantileSetKernel
public import QuantitativeFollowup.VectorScoreTail

@[expose] public section

/-! The precise threshold estimate of Lemma 3.1(e), for every measurable
quantile set of positive length (and hence every interval).  The threshold
is only an almost-everywhere condition; partial quantile atoms are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorCenteredKernelScore_eq_integral (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hiκ : Integrable κ (parisiFreeMeasure μ s))
    (z : VectorDisorderBrownianSample n×Configuration n) :
    vectorCenteredKernelScore μ s β t ht κ z=
      ∫q,κ q*(vectorMeasureOverlapScore μ β t ht q z-(q:ℝ)/2) ∂parisiFreeMeasure μ s := by
  have hscore : Integrable (fun q=>κ q*vectorMeasureOverlapScore μ β t ht q z) (parisiFreeMeasure μ s) := by
    apply (hiκ.norm.const_mul (3/2)).mono'
      (hκ.mul (continuous_vectorMeasureOverlapScore_path μ β t ht z).measurable).aestronglyMeasurable
    exact .of_forall fun q=>by
      change ‖κ q*vectorMeasureOverlapScore μ β t ht q z‖≤(3/2)*‖κ q‖
      rw [norm_mul]
      have hb : ‖vectorMeasureOverlapScore μ β t ht q z‖≤3/2 := by
        simpa only [Real.norm_eq_abs] using vectorMeasureOverlapScore_bound μ β t ht q z
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have hlevel : Integrable (fun q=>κ q*(q:ℝ)) (parisiFreeMeasure μ s) := by
    apply hiκ.norm.mono' (hκ.mul measurable_subtype_coe).aestronglyMeasurable
    exact .of_forall fun q=>by
      change ‖κ q*(q:ℝ)‖≤‖κ q‖
      rw [norm_mul,Real.norm_of_nonneg q.property.1]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left q.property.2 (norm_nonneg _)
  unfold vectorCenteredKernelScore vectorMeasureWeightedOverlapScore vectorKernelOverlapLevel
  simp_rw [mul_sub,←mul_div_assoc]
  rw [integral_sub hscore (hlevel.div_const 2),integral_div]

theorem vectorCenteredQuantileSetScore_eq_integral (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (I : Set ℝ) (x : ℝ)
    (hI : I⊆Ioc (0:ℝ) (1-s)) (hx : 0<x)
    (z : VectorDisorderBrownianSample n×Configuration n) :
    vectorCenteredKernelScore μ s β t ht (quantileSetKernel μ s I x) z=
      x⁻¹*(∫v in I,vectorMeasureOverlapScore μ β t ht (parisiFreeQuantile μ s v) z-
        (parisiFreeQuantile μ s v:ℝ)/2) := by
  rw [vectorCenteredKernelScore_eq_integral μ s β t ht _ (measurable_quantileSetKernel μ s I x)
    ((memLp_quantileSetKernel μ s I x hx).integrable one_le_two)]
  exact integral_quantileSetKernel_smul μ s I x hI _
    ((continuous_vectorMeasureOverlapScore_path μ β t ht z).measurable.sub
      (measurable_subtype_coe.div_const 2))

theorem vectorKernelOverlapLevel_quantileSet (μ : Paper.ParisiMeasure) (s : ℝ)
    (I : Set ℝ) (x : ℝ) (hI : I⊆Ioc (0:ℝ) (1-s)) :
    vectorKernelOverlapLevel μ s (quantileSetKernel μ s I x)=
      x⁻¹*(∫v in I,(parisiFreeQuantile μ s v:ℝ)) :=
  integral_quantileSetKernel_smul μ s I x hI _ measurable_subtype_coe

theorem quantileSetKernel_threshold_cost (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (I : Set ℝ) (x u : ℝ) (hI : I⊆Ioc (0:ℝ) (1-s)) (hx : 0<x)
    (hlen : volume.real I=x) (hu : 0<u)
    (hthreshold : ∀ᵐv ∂volume.restrict I,u≤Paper.parisiCDF μ (parisiFreeQuantile μ s v)) :
    (∫q,quantileSetKernel μ s I x q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s)≤1/(x*u) := by
  have hi:=integrable_kernel_square_div_cdf μ s hs.1 hμ (quantileSetKernel μ s I x)
    (measurable_quantileSetKernel μ s I x) (1/x) (by positivity)
    (fun q=>by rw [abs_of_nonneg (quantileSetKernel_nonneg_le μ s I x hx q).1]
               exact (quantileSetKernel_nonneg_le μ s I x hx q).2)
  have hκL:=memLp_quantileSetKernel μ s I x hx
  have hbound : (fun q=>quantileSetKernel μ s I x q^2/Paper.parisiCDF μ q)
      ≤ᵐ[parisiFreeMeasure μ s] fun q=>quantileSetKernel μ s I x q/(x*u) := by
    filter_upwards [ae_quantileSetKernel_threshold μ s I x u hI hthreshold] with q hq
    by_cases hz : quantileSetKernel μ s I x q=0
    · simp only [hz,zero_pow (by norm_num : (2:ℕ)≠0),zero_div,le_refl]
    · have hCDF:=hq hz
      have hκ:=quantileSetKernel_nonneg_le μ s I x hx q
      have hsq : quantileSetKernel μ s I x q^2≤quantileSetKernel μ s I x q/x := by
        have h:=mul_le_mul_of_nonneg_left hκ.2 hκ.1
        simpa only [mul_one_div,←pow_two] using h
      calc
        _≤quantileSetKernel μ s I x q^2/u :=
          div_le_div_of_nonneg_left (sq_nonneg _) hu hCDF
        _≤(quantileSetKernel μ s I x q/x)/u :=div_le_div_of_nonneg_right hsq hu.le
        _=quantileSetKernel μ s I x q/(x*u) :=by ring
  calc
    _≤∫q,quantileSetKernel μ s I x q/(x*u) ∂parisiFreeMeasure μ s :=
      integral_mono_ae hi ((hκL.integrable one_le_two).div_const _) hbound
    _=_ :=by rw [integral_div,integral_quantileSetKernel_normalized μ s I x hI hx hlen]

theorem vector_quantile_set_score_variance (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (I : Set ℝ) (x u : ℝ) (hI : I⊆Ioc (0:ℝ) (1-s)) (hx : 0<x)
    (hlen : volume.real I=x) (hu : 0<u)
    (hthreshold : ∀ᵐv ∂volume.restrict I,u≤Paper.parisiCDF μ (parisiFreeQuantile μ s v)) :
    variance (vectorCenteredKernelScore (n:=n) μ s β t ht.le (quantileSetKernel μ s I x))
      (vectorMeasureSpinPathLaw μ β t s ht.le)≤1/((n:ℝ)*((1-t)*β^2)*u*x) := by
  rw [variance_vectorCenteredKernelScore μ s β t s ht.le _ (measurable_quantileSetKernel μ s I x)]
  have hV:=vector_weighted_score_variance_L2 hn μ s β t hβ ht hs hμ hmin
    (quantileSetKernel μ s I x) (measurable_quantileSetKernel μ s I x)
    (fun q=>(quantileSetKernel_nonneg_le μ s I x hx q).1) (memLp_quantileSetKernel μ s I x hx)
  apply hV.trans
  have h:=mul_le_mul_of_nonneg_left
    (quantileSetKernel_threshold_cost μ s ⟨hs.1,hs.2.le⟩ hμ I x u hI hx hlen hu hthreshold)
    (show 0≤1/((n:ℝ)*((1-t)*β^2)) by positivity)
  convert h using 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end QuantitativeFollowup
