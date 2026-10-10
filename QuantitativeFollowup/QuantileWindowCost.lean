module
public import QuantitativeFollowup.QuantileWindowSupport
public import QuantitativeFollowup.VectorScoreVariance

@[expose] public section

/-! The actual window kernel has the reciprocal-CDF cost required by the
mean-direction estimate.  The minimizing-profile score variance then
provides the literal window variance with all atom-sensitive inputs proved. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem quantileWindowKernel_square_div_cdf_ae (μ : Paper.ParisiMeasure) (s v x u : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hv : v≤1-s) (hx : 0<x) (hu : 0<u)
    (hux : u≤ s+max 0 (v-x)) :
    (fun q=>quantileWindowKernel μ s v x q^2/Paper.parisiCDF μ q)≤ᵐ[parisiFreeMeasure μ s]
      fun q=>quantileWindowKernel μ s v x q/(x*u) := by
  filter_upwards [ae_quantileWindowKernel_cdf_lower μ s v x hs hv] with q hq
  by_cases hz : quantileWindowKernel μ s v x q=0
  · simp only [hz,zero_pow (by norm_num : (2:ℕ)≠0),zero_div,le_refl]
  · have hCDF : u≤Paper.parisiCDF μ q:=hux.trans (hq hz)
    have hκ:=quantileWindowKernel_nonneg_le μ s v x hx q
    have hsq : quantileWindowKernel μ s v x q^2≤quantileWindowKernel μ s v x q/x := by
      have h:=mul_le_mul_of_nonneg_left hκ.2 hκ.1
      simpa only [mul_one_div,←pow_two] using h
    calc
      _≤quantileWindowKernel μ s v x q^2/u :=
        div_le_div_of_nonneg_left (sq_nonneg _) hu hCDF
      _≤(quantileWindowKernel μ s v x q/x)/u :=
        div_le_div_of_nonneg_right hsq hu.le
      _=quantileWindowKernel μ s v x q/(x*u) := by ring

theorem quantileWindowKernel_cost_bound (μ : Paper.ParisiMeasure) (s v x u : ℝ)
    (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hv : v≤1-s) (hx : 0<x) (hu : 0<u)
    (hux : u≤ s+max 0 (v-x)) :
    (∫q,quantileWindowKernel μ s v x q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s)≤1/(x*u) := by
  have hi:=integrable_kernel_square_div_cdf μ s hs.1 hμ (quantileWindowKernel μ s v x)
    (measurable_quantileWindowKernel μ s v x) (1/x) (by positivity)
    (fun q=>by rw [abs_of_nonneg (quantileWindowKernel_nonneg_le μ s v x hx q).1]
               exact (quantileWindowKernel_nonneg_le μ s v x hx q).2)
  calc
    _≤∫q,quantileWindowKernel μ s v x q/(x*u) ∂parisiFreeMeasure μ s := by
      exact integral_mono_ae hi ((integrable_quantileWindowKernel μ s v x hx).div_const _)
        (quantileWindowKernel_square_div_cdf_ae μ s v x u ⟨hs.1.le,hs.2⟩ hv hx hu hux)
    _=(∫q,quantileWindowKernel μ s v x q ∂parisiFreeMeasure μ s)/(x*u) := integral_div _ _
    _≤1/(x*u) := div_le_div_of_nonneg_right (integral_quantileWindowKernel_le_one μ s v x hv hx)
      (mul_nonneg hx.le hu.le)

theorem quantileWindowKernel_half_cost_bound (μ : Paper.ParisiMeasure) (s v : ℝ)
    (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hv : v∈Ioc (0:ℝ) (1-s)) :
    (∫q,quantileWindowKernel μ s v ((s+v)/2) q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s)
      ≤4/(s+v)^2 := by
  have hx : 0<(s+v)/2:=by linarith [hs.1,hv.1]
  have hux : (s+v)/2≤ s+max 0 (v-(s+v)/2) := by
    have h:=le_max_right (0:ℝ) (v-(s+v)/2)
    linarith
  have h:=quantileWindowKernel_cost_bound μ s v ((s+v)/2) ((s+v)/2) hs hμ hv.2 hx hx hux
  convert h using 1
  field_simp
  ring

theorem vector_quantile_window_score_variance (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t v : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hv : v∈Ioc (0:ℝ) (1-s)) :
    variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le
      (quantileWindowKernel μ s v ((s+v)/2))) (vectorMeasureSpinPathLaw μ β t s ht.le)
      ≤4/((n:ℝ)*((1-t)*β^2)*(s+v)^2) := by
  have hx : 0<(s+v)/2:=by linarith [hs.1,hv.1]
  have hV:=vector_weighted_score_variance hn μ s β t hβ ht hs hμ hmin
    (quantileWindowKernel μ s v ((s+v)/2)) (measurable_quantileWindowKernel μ s v ((s+v)/2))
    (1/((s+v)/2)) (by positivity)
    (fun q=>by rw [abs_of_nonneg (quantileWindowKernel_nonneg_le μ s v ((s+v)/2) hx q).1]
               exact (quantileWindowKernel_nonneg_le μ s v ((s+v)/2) hx q).2)
  apply hV.trans
  have h:=mul_le_mul_of_nonneg_left (quantileWindowKernel_half_cost_bound μ s v ⟨hs.1,hs.2.le⟩ hμ hv)
    (show 0≤1/((n:ℝ)*((1-t)*β^2)) by positivity)
  convert h using 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end QuantitativeFollowup
