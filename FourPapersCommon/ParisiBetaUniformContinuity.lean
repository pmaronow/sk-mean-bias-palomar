module
public import FourPapersCommon.ParisiBetaContinuity
public import FourPapersCommon.WienerExponential
public import Paper.ParisiHJBValueFunction
public import Paper.DerivativeCompactness
public import FRSB.GlobalMeasureStability

@[expose] public section

/-! Uniform temperature continuity at every physical time. Comparing the
same actual restarted controls gives a uniform value bound. A finite-difference
estimate then gives uniform continuity of the actual spatial gradient. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace FourPapersCommon
open Paper
set_option maxHeartbeats 1000000

theorem integrable_norm_canonicalBrownianPath :
    Integrable (fun sample => ‖canonicalBrownianPath sample‖) canonicalBrownianMeasure := by
  apply (integrable_exp_norm_canonicalBrownianPath 1).mono' measurable_canonicalBrownianPath.norm.aestronglyMeasurable
  exact .of_forall fun sample => by
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    simpa using (Real.add_one_le_exp ‖canonicalBrownianPath sample‖).trans'
      (by linarith : ‖canonicalBrownianPath sample‖ ≤ ‖canonicalBrownianPath sample‖+1)

def parisiBrownianPathMoment : ℝ :=
  ∫sample,‖canonicalBrownianPath sample‖ ∂canonicalBrownianMeasure

theorem parisiBrownianPathMoment_nonneg : 0≤parisiBrownianPathMoment :=
  integral_nonneg (fun _=>norm_nonneg _)

def parisiBetaUniformError (β γ : ℝ) : ℝ :=
  |β-γ| *parisiBrownianPathMoment+(3/2 : ℝ)*|β^2-γ^2|

theorem parisiBetaUniformError_nonneg (β γ : ℝ) : 0≤parisiBetaUniformError β γ := by
  exact add_nonneg (mul_nonneg (abs_nonneg _) parisiBrownianPathMoment_nonneg) (by positivity)

theorem parisiBetaUniformError_symm (β γ : ℝ) :
    parisiBetaUniformError β γ=parisiBetaUniformError γ β := by
  simp only [parisiBetaUniformError,abs_sub_comm]

theorem parisiTimeControlPayoff_beta_sub_le (β γ x : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) (A : ℝ→BrownianSample→ℝ)
    (hA : IsParisiAdmissibleControl A) (sample : BrownianSample) :
    ‖(Real.log (Real.cosh (parisiTimeControlEndpoint β x μ a A sample))-
        parisiTimeControlCost β μ a A sample)-
      (Real.log (Real.cosh (parisiTimeControlEndpoint γ x μ a A sample))-
        parisiTimeControlCost γ μ a A sample)‖ ≤
      |β-γ| *‖canonicalBrownianPath sample‖+(3/2 : ℝ)*|β^2-γ^2| := by
  have hd : ‖∫r in (0 : ℝ)..(1-a),parisiCDF μ (a+r)*A r sample‖≤1 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0 : ℝ)) (b:=1-a)
      (C:=(1 : ℝ)) (f:=fun r=>parisiCDF μ (a+r)*A r sample) (fun r _=>by
        rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg μ _)]
        exact (mul_le_mul (parisiCDF_le_one μ _) (hA.bounded r sample)
          (norm_nonneg _) zero_le_one).trans_eq (mul_one _))
    simp only [sub_zero,abs_of_nonneg (sub_nonneg.mpr ha.2),one_mul] at hh
    linarith [ha.1]
  have hc : ‖∫r in (0 : ℝ)..(1-a),parisiCDF μ (a+r)*A r sample^2‖≤1 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0 : ℝ)) (b:=1-a)
      (C:=(1 : ℝ)) (f:=fun r=>parisiCDF μ (a+r)*A r sample^2) (fun r _=>by
        rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg μ _),norm_pow]
        have hsq : ‖A r sample‖^2≤1 := by nlinarith [hA.bounded r sample,norm_nonneg (A r sample)]
        exact (mul_le_mul (parisiCDF_le_one μ _) hsq (by positivity) zero_le_one).trans_eq (mul_one _))
    simp only [sub_zero,abs_of_nonneg (sub_nonneg.mpr ha.2),one_mul] at hh
    linarith [ha.1]
  have hB : ‖canonicalBrownian (1-a).toNNReal sample‖≤‖canonicalBrownianPath sample‖ := by
    simpa only [canonicalBrownianPath,ContinuousMap.coe_mk,Real.toNNReal_coe] using
      (canonicalBrownianPath sample).norm_coe_le_norm ⟨1-a,by constructor <;> linarith [ha.1,ha.2]⟩
  have he : parisiTimeControlEndpoint β x μ a A sample-parisiTimeControlEndpoint γ x μ a A sample =
      (β-γ)*canonicalBrownian (1-a).toNNReal sample+
        (β^2-γ^2)*(∫r in (0 : ℝ)..(1-a),parisiCDF μ (a+r)*A r sample) := by
    unfold parisiTimeControlEndpoint
    ring
  have hx : ‖parisiTimeControlEndpoint β x μ a A sample-parisiTimeControlEndpoint γ x μ a A sample‖≤
      |β-γ| *‖canonicalBrownianPath sample‖+|β^2-γ^2| := by
    rw [he]
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Real.norm_eq_abs]
    exact add_le_add (mul_le_mul_of_nonneg_left hB (abs_nonneg _))
      ((mul_le_mul_of_nonneg_left hd (abs_nonneg _)).trans_eq (mul_one _))
  have hcost : ‖parisiTimeControlCost β μ a A sample-parisiTimeControlCost γ μ a A sample‖≤
      |β^2-γ^2|/2 := by
    unfold parisiTimeControlCost
    simp_rw [mul_assoc,intervalIntegral.integral_const_mul]
    rw [←sub_mul,←sub_div,norm_mul,Real.norm_eq_abs,abs_div]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ)<2)]
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (mul_one _)
  have hlog := lipschitzWith_logcosh.dist_le_mul
    (parisiTimeControlEndpoint β x μ a A sample) (parisiTimeControlEndpoint γ x μ a A sample)
  simp only [dist_eq_norm,NNReal.coe_one,one_mul] at hlog
  have hp : (Real.log (Real.cosh (parisiTimeControlEndpoint β x μ a A sample))-
      parisiTimeControlCost β μ a A sample)-
      (Real.log (Real.cosh (parisiTimeControlEndpoint γ x μ a A sample))-
      parisiTimeControlCost γ μ a A sample) =
      (Real.log (Real.cosh (parisiTimeControlEndpoint β x μ a A sample))-
      Real.log (Real.cosh (parisiTimeControlEndpoint γ x μ a A sample)))-
      (parisiTimeControlCost β μ a A sample-parisiTimeControlCost γ μ a A sample) := by ring
  rw [hp]
  exact (norm_sub_le _ _).trans (by linarith)

theorem parisiTimeControlObjective_beta_sub_le (β γ x : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) (A : ℝ→BrownianSample→ℝ)
    (hA : IsParisiAdmissibleControl A) :
    ‖parisiTimeControlObjective β x μ a A-parisiTimeControlObjective γ x μ a A‖≤
      parisiBetaUniformError β γ := by
  have hi (b : ℝ) : Integrable (fun sample=>Real.log (Real.cosh (parisiTimeControlEndpoint b x μ a A sample))-parisiTimeControlCost b μ a A sample) canonicalBrownianMeasure := (integrable_parisiTimeControl_terminal b x μ a ha A hA).sub
    (integrable_parisiTimeControlCost b μ a ha A hA)
  unfold parisiTimeControlObjective
  rw [←integral_sub (hi β) (hi γ)]
  have hh := norm_integral_le_of_norm_le
    ((integrable_norm_canonicalBrownianPath.const_mul |β-γ|).add
      (integrable_const ((3/2 : ℝ)*|β^2-γ^2|)))
    (.of_forall fun sample=>parisiTimeControlPayoff_beta_sub_le β γ x μ a ha A hA sample)
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_norm_canonicalBrownianPath.const_mul |β-γ|)
    (integrable_const _),integral_const_mul] at hh
  simpa only [parisiBetaUniformError,parisiBrownianPathMoment,integral_const,probReal_univ,
    smul_eq_mul,mul_one,one_mul] using hh

theorem parisiPotential_beta_uniform_sub_le (β γ : ℝ) (hβ : β≠0) (hγ : γ≠0)
    (μ : ParisiMeasure) (a x : ℝ) (ha : a∈Icc (0 : ℝ) 1) :
    ‖parisiPotential β μ (a,x)-parisiPotential γ μ (a,x)‖≤parisiBetaUniformError β γ := by
  have hup (b c : ℝ) (hb : b≠0) (hc : c≠0) :
      parisiPotential b μ (a,x)-parisiPotential c μ (a,x)≤parisiBetaUniformError b c := by
    let A := canonicalParisiRestartControl b x μ a ha.1
    have hA := isParisiAdmissibleControl_canonicalParisiRestartControl b x μ a ha.1
    have he := parisiTimeControlObjective_feedback_eq_potential b x hb μ a ha
    have hl := parisiTimeControlObjective_le_potential c x hc μ a ha A hA
    have hh := parisiTimeControlObjective_beta_sub_le b c x μ a ha A hA
    have hr := (le_abs_self _).trans hh
    change parisiTimeControlObjective b x μ a A=_ at he
    rw [Real.norm_eq_abs] at hh
    linarith
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · have hh := hup γ β hγ hβ
    rw [parisiBetaUniformError_symm] at hh
    linarith
  · exact hup β γ hβ hγ

theorem tendsto_parisiBetaUniformError {ι : Type*} {L : Filter ι} (γ : ℝ) (β : ι→ℝ)
    (hβ : Tendsto β L (𝓝 γ)) : Tendsto (fun i=>parisiBetaUniformError (β i) γ) L (𝓝 0) := by
  have h₁ : Tendsto (fun i=>|β i-γ|) L (𝓝 (0 : ℝ)) := by simpa using (hβ.sub_const γ).abs
  have h₂ : Tendsto (fun i=>|β i^2-γ^2|) L (𝓝 (0 : ℝ)) := by
    convert ((hβ.pow 2).sub_const (γ^2)).abs using 1; simp
  simpa only [parisiBetaUniformError,zero_mul,mul_zero,zero_add] using
    (h₁.mul_const parisiBrownianPathMoment).add (h₂.const_mul (3/2 : ℝ))

theorem norm_parisiGradient_beta_sub_le (β γ : ℝ) (hβ : β≠0) (hγ : γ≠0)
    (μ : ParisiMeasure) (a x δ : ℝ) (ha : a∈Icc (0 : ℝ) 1) (hδ : 0<δ) :
    ‖parisiGradient β μ (a,x)-parisiGradient γ μ (a,x)‖≤
      2*δ+2*parisiBetaUniformError β γ/δ := by
  rw [Real.norm_eq_abs]
  simpa only [NNReal.coe_one,mul_one] using abs_derivatives_sub_le_of_uniform_bound
    (fun y=>hasDerivAt_parisiPotential_spatial_all β μ a y ha)
    (fun y=>hasDerivAt_parisiPotential_spatial_all γ μ a y ha)
    (lipschitzWith_parisiGradient_all β μ a) (lipschitzWith_parisiGradient_all γ μ a)
    (fun y=>by simpa only [Real.norm_eq_abs] using parisiPotential_beta_uniform_sub_le β γ hβ hγ μ a y ha)
    x hδ

theorem norm_parisiGradientBCF_beta_sub_le (β γ : ℝ) (hβ : β≠0) (hγ : γ≠0)
    (μ : ParisiMeasure) {δ : ℝ} (hδ : 0<δ) :
    ‖parisiGradientBCF β μ-parisiGradientBCF γ μ‖≤2*δ+2*parisiBetaUniformError β γ/δ := by
  apply (BoundedContinuousFunction.norm_le (by positivity [parisiBetaUniformError_nonneg β γ])).mpr
  intro p
  simp only [BoundedContinuousFunction.sub_apply,parisiGradientBCF_apply]
  exact norm_parisiGradient_beta_sub_le β γ hβ hγ μ p.1 p.2 δ p.1.property hδ

theorem tendsto_parisiGradientBCF_of_temperature {ι : Type*} {L : Filter ι}
    (β : ι→ℝ) (γ : ℝ) (hγ : γ≠0) (hβ : Tendsto β L (𝓝 γ))
    (μ : ParisiMeasure) :
    Tendsto (fun i=>parisiGradientBCF (β i) μ) L (𝓝 (parisiGradientBCF γ μ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/8
  have hδ : 0<δ := by dsimp [δ]; positivity
  have he := (tendsto_parisiBetaUniformError γ β hβ).eventually
    (gt_mem_nhds (show 0<ε*δ/8 by positivity))
  have hb := hβ.eventually (eventually_ne_nhds hγ)
  filter_upwards [he,hb] with i hi hbi
  rw [dist_eq_norm]
  apply (norm_parisiGradientBCF_beta_sub_le (β i) γ hbi hγ μ hδ).trans_lt
  have ht : 2*parisiBetaUniformError (β i) γ/δ<ε/4 := by
    apply (div_lt_iff₀ hδ).mpr
    nlinarith
  dsimp [δ] at *
  linarith

theorem tendsto_parisiGradientBCF_of_temperature_and_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ι→ℝ) (γ : ℝ) (hγ : γ≠0) (hβ : Tendsto β L (𝓝 γ))
    (μn : ι→ParisiMeasure) (μ : ParisiMeasure) (hμ : Tendsto μn L (𝓝 μ)) :
    Tendsto (fun i=>parisiGradientBCF (β i) (μn i)) L (𝓝 (parisiGradientBCF γ μ)) := by
  have hg := (FRSB.continuous_gradientBCF γ).continuousAt.tendsto.comp hμ
  have he : Tendsto (fun i=>dist (parisiGradientBCF (β i) (μn i))
      (parisiGradientBCF γ (μn i))) L (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ := ε/8
    have hδ : 0<δ := by dsimp [δ]; positivity
    have herror := (tendsto_parisiBetaUniformError γ β hβ).eventually
      (gt_mem_nhds (show 0<ε*δ/8 by positivity))
    have hb := hβ.eventually (eventually_ne_nhds hγ)
    filter_upwards [herror,hb] with i hi hbi
    simp only [dist_eq_norm,sub_zero,norm_norm]
    apply (norm_parisiGradientBCF_beta_sub_le (β i) γ hbi hγ (μn i) hδ).trans_lt
    have ht : 2*parisiBetaUniformError (β i) γ/δ<ε/4 := by
      apply (div_lt_iff₀ hδ).mpr
      nlinarith
    dsimp [δ] at *
    linarith
  exact tendsto_of_tendsto_of_dist hg (by simpa only [Function.comp_def,dist_comm] using he)

end FourPapersCommon
