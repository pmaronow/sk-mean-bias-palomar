module
public import QuantitativeFollowup.QuantileWindowCost

@[expose] public section

/-! The genuine quarter-window score variance is at most 6/(M(s+v)^2). -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem quarter_window_kernel_cost_bound (μ : Paper.ParisiMeasure) (s v : ℝ)
    (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hv : v∈Ioc (0:ℝ) (1-s)) :
    (∫q,quantileWindowKernel μ s v ((s+v)/4) q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s)
      ≤6/(s+v)^2 := by
  have hx : 0<(s+v)/4:=by linarith [hs.1,hv.1]
  have hu : 0<3*(s+v)/4:=by linarith [hs.1,hv.1]
  have hux : 3*(s+v)/4≤ s+max 0 (v-(s+v)/4) := by
    have h:=le_max_right (0:ℝ) (v-(s+v)/4)
    linarith
  have h:=quantileWindowKernel_cost_bound μ s v ((s+v)/4) (3*(s+v)/4) hs hμ hv.2 hx hu hux
  apply h.trans
  have hden : 0<(s+v)^2:=sq_pos_of_pos (by linarith [hs.1,hv.1])
  calc
    1/(((s+v)/4)*(3*(s+v)/4))=(16/3)/(s+v)^2 := by field_simp;ring
    _≤6/(s+v)^2 := div_le_div_of_nonneg_right (by norm_num : (16/3:ℝ)≤6) hden.le

theorem vector_quarter_window_score_variance (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t v : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hv : v∈Ioc (0:ℝ) (1-s)) :
    variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le
      (quantileWindowKernel μ s v ((s+v)/4))) (vectorMeasureSpinPathLaw μ β t s ht.le)
      ≤6/((n:ℝ)*((1-t)*β^2)*(s+v)^2) := by
  have hx : 0<(s+v)/4:=by linarith [hs.1,hv.1]
  have hV:=vector_weighted_score_variance hn μ s β t hβ ht hs hμ hmin
    (quantileWindowKernel μ s v ((s+v)/4)) (measurable_quantileWindowKernel μ s v ((s+v)/4))
    (1/((s+v)/4)) (by positivity)
    (fun q=>by rw [abs_of_nonneg (quantileWindowKernel_nonneg_le μ s v ((s+v)/4) hx q).1]
               exact (quantileWindowKernel_nonneg_le μ s v ((s+v)/4) hx q).2)
  apply hV.trans
  have h:=mul_le_mul_of_nonneg_left (quarter_window_kernel_cost_bound μ s v ⟨hs.1,hs.2.le⟩ hμ hv)
    (show 0≤1/((n:ℝ)*((1-t)*β^2)) by positivity)
  convert h using 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end HexagonPaper
