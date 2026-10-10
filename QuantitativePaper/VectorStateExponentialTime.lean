module
public import QuantitativePaper.VectorBrownianExponentialTime
public import QuantitativePaper.VectorFiniteExponentialLocalization
public import QuantitativePaper.VectorTiltedBrownian

@[expose] public section

/-! Space-time exponential localization of the actual finite and measure
vector diffusions. Fubini uses the genuine Gaussian marginal estimate and
a deterministic drift bound, rather than an assumed stopping-time formula. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set StochasticCalculus
open scoped NNReal ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem integral_exp_vectorBrownian_norm_le (K : ℝ) (r : ℝ≥0) (hr : r≤1) :
    (∫sample : VectorBrownianSample n,Real.exp (K*‖vectorBrownian r sample‖)
      ∂vectorBrownianMeasure n)≤vectorGaussianNormLaplace n |K| := by
  have he:=(measurePreserving_snd (μ := completionLaw n)
    (ν := vectorBrownianMeasure n)).hasLaw.integral_comp
    (f := fun sample=>Real.exp (K*‖vectorBrownian r sample‖))
    ((Real.measurable_exp.comp ((measurable_vectorBrownian r).norm.const_mul K)).aestronglyMeasurable)
  exact he.symm.trans_le (integral_exp_disorderVectorBrownian_norm_le K r hr)

theorem integrable_time_exp_bounded_vectorState (P : Measure (Couplings n×ℝ))
    [IsProbabilityMeasure P] (X : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (hX : Measurable (Function.uncurry X)) (B σ K : ℝ) (hσ : 0≤σ)
    (hP : Integrable (fun p=>Real.exp (|K| *‖p‖)) P)
    (hbound : ∀r : ℝ≥0,r≤1→∀sample,‖X r sample‖≤B+σ*‖vectorBrownian r sample.2‖) :
    Integrable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      Real.exp (K*(‖z.2.1‖+‖X z.1 z.2‖)))
      ((nonnegativeLebesgueMeasure.restrict (Ioc 0 1)).prod (P.prod (vectorBrownianMeasure n))) := by
  let ν:=nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) 1)
  letI : IsFiniteMeasure ν:=⟨by simpa only [ν,Measure.restrict_apply_univ] using
    (lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1))⟩
  let f : ℝ≥0→VectorDisorderBrownianSample n→ℝ :=
    fun r sample=>Real.exp (K*(‖sample.1‖+‖X r sample‖))
  let g : ℝ≥0→VectorDisorderBrownianSample n→ℝ := fun r sample=>
    Real.exp (|K| *B)*(Real.exp (|K| *‖sample.1‖)*Real.exp ((|K| *σ)*‖vectorBrownian r sample.2‖))
  have hm : Measurable (Function.uncurry f):=
    Real.measurable_exp.comp (((measurable_fst.comp measurable_snd).norm.add hX.norm).const_mul K)
  have hg (r : ℝ≥0) : Integrable (g r) (P.prod (vectorBrownianMeasure n)):=
    (hP.mul_prod (integrable_exp_vectorBrownian_norm r (|K| *σ))).const_mul _
  have hfg (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
      ‖f r sample‖≤g r sample := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    dsimp only [f,g]
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hb:=hbound r hr sample
    have hk:=mul_le_mul_of_nonneg_right (le_abs_self K)
      (add_nonneg (norm_nonneg sample.1) (norm_nonneg (X r sample)))
    have hh:=mul_le_mul_of_nonneg_left (add_le_add (le_refl ‖sample.1‖) hb) (abs_nonneg K)
    nlinarith only [hk,hh]
  have hf (r : ℝ≥0) (hr : r≤1) : Integrable (f r) (P.prod (vectorBrownianMeasure n)):=
    (hg r).mono' (hm.of_uncurry_left.aestronglyMeasurable) (.of_forall (hfg r hr))
  have hiP : 0≤∫p,Real.exp (|K| *‖p‖)∂P:=integral_nonneg fun _=>(Real.exp_pos _).le
  let C:=Real.exp (|K| *B)*(∫p,Real.exp (|K| *‖p‖)∂P)*vectorGaussianNormLaplace n (|K| *σ)
  have hi (r : ℝ≥0) (hr : r≤1) :
      (∫sample,‖f r sample‖∂P.prod (vectorBrownianMeasure n))≤C := by
    calc
      _ ≤ ∫sample,g r sample∂P.prod (vectorBrownianMeasure n) :=
        integral_mono (hf r hr).norm (hg r) (hfg r hr)
      _ = Real.exp (|K| *B)*(∫p,Real.exp (|K| *‖p‖)∂P)*
          (∫sample,Real.exp ((|K| *σ)*‖vectorBrownian r sample‖)∂vectorBrownianMeasure n) := by
        change (∫sample,Real.exp (|K| *B)*(Real.exp (|K| *‖sample.1‖)*
          Real.exp ((|K| *σ)*‖vectorBrownian r sample.2‖))∂P.prod (vectorBrownianMeasure n))=_
        rw [integral_const_mul]
        rw [integral_prod_mul (fun p : Couplings n×ℝ=>Real.exp (|K| *‖p‖))
          (fun sample : VectorBrownianSample n=>Real.exp ((|K| *σ)*‖vectorBrownian r sample‖))]
        ring
      _ ≤ C := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.exp_pos _).le hiP)
        simpa only [abs_of_nonneg (mul_nonneg (abs_nonneg _) hσ)] using
          integral_exp_vectorBrownian_norm_le (|K| *σ) r hr
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hf r hr.2
  · apply (integrable_const C).mono'
      hm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_of_nonneg (integral_nonneg fun _=>norm_nonneg _)]
    exact hi r hr.2

end QuantitativePaper
