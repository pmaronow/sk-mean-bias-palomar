module
public import Lemmas.SpinGlass.gaussian_concentration
public import Paper.GaussianIBP
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-! Exact absolute first moment of Gaussian projections, used in the
rotation proof of the dimension-independent Gaussian L¹ inequality. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1200000

theorem integral_abs_standardGaussian :
    (∫ x:ℝ,|x| ∂gaussianReal 0 1)=Real.sqrt (2/Real.pi) := by
  have ht : Tendsto (fun x:ℝ=>gaussianPDFReal 0 1 x) atTop (𝓝 0) := by
    have hpow : Tendsto (fun x:ℝ=>x^2) atTop atTop := tendsto_pow_atTop (by norm_num)
    have hex := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hpow.const_mul_atTop (by norm_num : 0<(1/2:ℝ))))
    have hh := hex.const_mul (Real.sqrt (2*Real.pi))⁻¹
    convert hh using 1
    · funext x
      simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one,Function.comp_apply]
      congr 2
      ring
    · simp only [mul_zero]
  have hi := Paper.integrable_mul_standardGaussianPDF
  have hhalf := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a:=0) (f:=gaussianPDFReal 0 1) (f':=fun x=>-x*gaussianPDFReal 0 1 x)
    (fun x _=>Paper.hasDerivAt_standardGaussianPDF x) (by
      convert hi.neg.integrableOn using 1
      funext x
      dsimp
      ring) ht
  have hhalf' : (∫ x:ℝ in Ioi 0,x*gaussianPDFReal 0 1 x)=
      (Real.sqrt (2*Real.pi))⁻¹ := by
    have he : (fun x:ℝ=>-x*gaussianPDFReal 0 1 x)=
        (fun x:ℝ=>-(x*gaussianPDFReal 0 1 x)) := by funext x; ring
    rw [he,integral_neg] at hhalf
    have hp0 : gaussianPDFReal 0 1 0=(Real.sqrt (2*Real.pi))⁻¹ := by
      norm_num [gaussianPDFReal]
    rw [hp0] at hhalf
    linarith
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0)≠0)]
  have he : (fun x:ℝ=>gaussianPDFReal 0 1 x • |x|)=
      (fun x:ℝ=>|x| * gaussianPDFReal 0 1 |x|) := by
    funext x
    simp [gaussianPDFReal,sq_abs,smul_eq_mul,mul_comm]
  rw [he]
  change (∫ x:ℝ,(fun z:ℝ=>z*gaussianPDFReal 0 1 z) |x|)=_
  have habs := integral_comp_abs (f:=fun z:ℝ=>z*gaussianPDFReal 0 1 z)
  rw [habs,hhalf']
  have hpi : 0<Real.pi := Real.pi_pos
  have h1 := Real.sq_sqrt (show 0≤2*Real.pi by positivity)
  have h2 := Real.sq_sqrt (show 0≤2/Real.pi by positivity)
  have hp : 0<Real.sqrt (2*Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hq : 0≤Real.sqrt (2/Real.pi) := Real.sqrt_nonneg _
  apply (sq_eq_sq₀ (by positivity) hq).mp
  rw [mul_pow,inv_pow,h1,h2]
  field_simp

/-- Exact Gaussian projection law with its actual standard Gaussian measure. -/
theorem integral_abs_stdGaussian_dual {E:Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L:StrongDual ℝ E) :
    (∫ x,|L x| ∂stdGaussian E)=Real.sqrt (2/Real.pi)*‖L‖ := by
  have hLaw := (IsGaussian.hasGaussianLaw_id (μ:=stdGaussian E)).map L
  have hmap : (stdGaussian E).map L=gaussianReal 0 (‖L‖^2).toNNReal := by
    simpa only [Function.comp_def,id_eq,integral_strongDual_stdGaussian,
      variance_dual_stdGaussian] using hLaw.map_eq_gaussianReal
  have hscale : gaussianReal 0 (‖L‖^2).toNNReal=(gaussianReal 0 1).map (fun x:ℝ=>‖L‖*x) := by
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero,mul_one]
    congr 1
    ext
    simp [Real.toNNReal_of_nonneg (sq_nonneg _)]
  rw [← integral_map L.continuous.aemeasurable (by fun_prop),hmap,hscale,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul,abs_of_nonneg (norm_nonneg L)]
  rw [integral_const_mul,integral_abs_standardGaussian,mul_comm]

theorem integral_abs_stdGaussian_inner {E:Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v:E) : (∫ x,|inner ℝ v x| ∂stdGaussian E)=Real.sqrt (2/Real.pi)*‖v‖ := by
  simpa using integral_abs_stdGaussian_dual ((InnerProductSpace.toDual ℝ E) v)

end FourPapersCommon
