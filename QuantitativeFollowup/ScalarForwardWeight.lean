module
public import QuantitativeFollowup.ScalarPostSupport
public import FRSB.ForwardProposition
public import Paper.HeatContraction

@[expose] public section

/-! The actual zero-field forward density divided by cosh is even and
nonincreasing with distance from zero once the scalar profile is one.
Its integrability and heat-contraction hypotheses are discharged here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB
open scoped NNReal ENNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 2200000

def scalarForwardCoshWeight (beta : ℝ) (μ : Paper.ParisiMeasure) (r : ℝ)
    (hr : r∈Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  forwardBridgeDensity beta μ r hr x/Real.cosh x

theorem integrable_scalarForwardCoshWeight (beta : ℝ) (hb : beta≠0)
    (μ : Paper.ParisiMeasure) (r : ℝ) (hr : r∈Ioc (0 : ℝ) 1) :
    Integrable (scalarForwardCoshWeight beta μ r hr) := by
  convert (integrable_forwardBridgeDensity beta hb μ r hr).mul_bdd
    continuous_sech.measurable.aestronglyMeasurable
    (.of_forall fun x=>show ‖sech x‖≤(1 : ℝ) by
      rw [Real.norm_of_nonneg (sech_pos x).le]
      exact sech_le_one x) using 1
  funext x
  unfold scalarForwardCoshWeight sech
  ring

theorem scalarForwardCoshWeight_even (beta : ℝ) (μ : Paper.ParisiMeasure)
    (r : ℝ) (hr : r∈Ioc (0 : ℝ) 1) (x : ℝ) :
    scalarForwardCoshWeight beta μ r hr (-x)=scalarForwardCoshWeight beta μ r hr x := by
  simp only [scalarForwardCoshWeight,forwardBridgeDensity_even,Real.cosh_neg]

theorem forwardRightPotential_monotone_positive (beta : ℝ) (hb : beta≠0)
    (μ : Paper.ParisiMeasure) (r : ℝ) (hr : r∈Ioc (0 : ℝ) 1) :
    MonotoneOn (forwardRightPotential beta μ r hr) (Ici (0 : ℝ)) := by
  let W := forwardRightPotential beta μ r hr
  have hW := contDiff_forwardRightPotential beta hb μ r hr
  have hd : Differentiable ℝ (deriv W) := by
    simpa only [iteratedDeriv_one] using hW.differentiable_iteratedDeriv 1 (by simp)
  have hc : ConvexOn ℝ univ W := convexOn_univ_of_deriv2_nonneg
    (hW.differentiable (by simp)) hd (fun x=>by
      have hh := (forwardRightPotential_curvature_bounds beta hb μ r hr x).1
      have hp : 0≤1/(beta^2*r) := one_div_nonneg.mpr (mul_nonneg (sq_nonneg beta) hr.1.le)
      exact hp.trans (by simpa only [←iteratedDeriv_eq_iterate] using hh))
  have hm := hc.monotoneOn_deriv (fun x _=>hW.differentiable (by simp) x)
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hW.continuous.continuousOn
    ((hW.differentiable (by simp)).differentiableOn)
  intro x hx
  have hx0 : 0≤x := interior_subset hx
  have he := hm (mem_univ 0) (mem_univ x) hx0
  simpa only [W,forwardRightPotential_deriv_origin] using he

theorem scalarForwardCoshWeight_eq_exponential (beta : ℝ) (hb : 0<beta)
    (μ : Paper.ParisiMeasure) (q r : ℝ) (hq : 0≤q)
    (hsupp : parisiSupport μ=Icc (0 : ℝ) q) (hr : r∈Ioc (0 : ℝ) 1) (hqr : q≤r)
    (x : ℝ) : scalarForwardCoshWeight beta μ r hr x=
      Real.exp (beta^2*(1-r)/2-forwardRightPotential beta μ r hr x) := by
  have hp := forwardBridgeDensity_pos beta hb.ne' μ r hr x
  unfold scalarForwardCoshWeight forwardRightPotential
  rw [parisiCDF_one_after_support_interval μ q hsupp r hqr,one_mul,
    parisiPotential_after_support_interval beta hb μ q r x hq hsupp ⟨hqr,hr.2⟩]
  have he : beta^2*(1-r)/2-(Real.log (Real.cosh x)+beta^2*(1-r)/2-
      Real.log (forwardBridgeDensity beta μ r hr x))=
      Real.log (forwardBridgeDensity beta μ r hr x)-Real.log (Real.cosh x) := by ring
  rw [he,Real.exp_sub,Real.exp_log hp,Real.exp_log (Real.cosh_pos x)]

theorem scalarForwardCoshWeight_antitone_positive (beta : ℝ) (hb : 0<beta)
    (μ : Paper.ParisiMeasure) (q r : ℝ) (hq : 0≤q)
    (hsupp : parisiSupport μ=Icc (0 : ℝ) q) (hr : r∈Ioc (0 : ℝ) 1) (hqr : q≤r) :
    AntitoneOn (scalarForwardCoshWeight beta μ r hr) (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  rw [scalarForwardCoshWeight_eq_exponential beta hb μ q r hq hsupp hr hqr x,
    scalarForwardCoshWeight_eq_exponential beta hb μ q r hq hsupp hr hqr y]
  exact Real.exp_le_exp.mpr (sub_le_sub_left
    (forwardRightPotential_monotone_positive beta hb.ne' μ r hr hx hy hxy) _)

theorem scalarForwardCoshWeight_doob_fourth_decay (beta : ℝ) (hb : 0<beta)
    (μ : Paper.ParisiMeasure) (q r : ℝ) (hq : 0≤q)
    (hsupp : parisiSupport μ=Icc (0 : ℝ) q) (hr : r∈Ioc (0 : ℝ) 1) (hqr : q≤r)
    (v : ℝ≥0) (hv : v≠0) :
    (∫x,forwardBridgeDensity beta μ r hr x*doobOperator v (fun y=>sech y^4) x)≤
      Real.exp (-(v : ℝ)/2)*(∫x,forwardBridgeDensity beta μ r hr x*sech x^4) := by
  have he := gaussian_heat_exponential_decay v hv (scalarForwardCoshWeight beta μ r hr)
    (fun y=>sech y^3) (integrable_scalarForwardCoshWeight beta hb.ne' μ r hr)
    measurable_sech_cube 1 sech_cube_bound
    (sech_cube_comonotone (scalarForwardCoshWeight_even beta μ r hr)
      (scalarForwardCoshWeight_antitone_positive beta hb μ q r hq hsupp hr hqr))
  have hLeft : (∫x,forwardBridgeDensity beta μ r hr x*doobOperator v (fun y=>sech y^4) x)=
      Real.exp (-(v : ℝ)/2)*(∫x,scalarForwardCoshWeight beta μ r hr x*
        kernelAverage (μ:=volume) (heatKernel v) (fun y=>sech y^3) x) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [doobOperator_sech_fourth_eq_heat v hv]
    unfold scalarForwardCoshWeight
    ring
  have hRight : (∫x,scalarForwardCoshWeight beta μ r hr x*sech x^3)=
      ∫x,forwardBridgeDensity beta μ r hr x*sech x^4 := by
    apply integral_congr_ae
    filter_upwards with x
    unfold scalarForwardCoshWeight sech
    ring
  rw [←hLeft,hRight] at he
  exact he

end QuantitativeFollowup
