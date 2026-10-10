module
public import QuantitativePaper.VectorExponentialItoLocalizations
public import QuantitativePaper.VectorItoGenerator

@[expose] public section

/-! The literal generator of a smooth exponential-growth observable and
the genuine convergence of compactly localized generators. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorExponentialGenerator (f : VectorCompactTestParameter n→ℝ)
    (X d : ℝ≥0→VectorDisorderBrownianSample n→Field n) (σ : ℝ)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : ℝ :=
  fderiv ℝ (fun y=>f (r,(sample.1,y))) (X r sample) (d r sample)+
    σ^2/2*vectorBilinearTrace (vectorHessian (fun y=>f (r,(sample.1,y))) (X r sample))+
    vectorCompactSmoothTimeField f (r,(sample.1,X r sample))

theorem measurable_vectorExponentialGenerator
    (f : VectorCompactTestParameter n→ℝ) (hf : ContDiff ℝ ∞ f)
    {X d : ℝ≥0→VectorDisorderBrownianSample n→Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ) :
    Measurable (Function.uncurry (vectorExponentialGenerator f X d σ)) := by
  have hm : Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      ((z.1:ℝ),(z.2.1,X z.1 z.2))):=
    (NNReal.continuous_coe.measurable.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).prodMk hc.measurable_state)
  have hgrad:=(continuous_fderiv_vectorCompactSmooth_section hf).measurable.comp hm
  have hhess:=(continuous_vectorHessian_vectorCompactSmooth_section hf).measurable.comp hm
  have htrace : Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      vectorBilinearTrace (vectorHessian (fun y=>f (z.1,(z.2.1,y))) (X z.1 z.2))) := by
    unfold vectorBilinearTrace
    exact Finset.measurable_sum Finset.univ fun i _=>
      (show Measurable (fun H : Field n→L[ℝ]Field n→L[ℝ]ℝ=>
        H (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) from by fun_prop).comp hhess
  have hlinear := (show Measurable (fun z : (Field n→L[ℝ]ℝ)×Field n=>z.1 z.2)
    from (continuous_fst.clm_apply continuous_snd).measurable).comp
      (hgrad.prodMk hc.measurable_drift)
  exact (hlinear.add (measurable_const.mul htrace)).add
    ((contDiff_vectorCompactSmoothTimeField hf).continuous.measurable.comp hm)

theorem vectorItoGenerator_compactSmooth_eq
    (f : VectorCompactTestParameter n→ℝ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (T : ℝ≥0) (X d : ℝ≥0→VectorDisorderBrownianSample n→Field n) (σ : ℝ) :
    vectorItoGenerator (vectorCompactSmoothSampleTimeData f hf hs T) X d σ=
      vectorExponentialGenerator f X d σ := rfl

theorem vectorExponentialLocalizedGenerator_eventually_eq
    (f : VectorCompactTestParameter n→ℝ)
    (X d : ℝ≥0→VectorDisorderBrownianSample n→Field n) (σ : ℝ)
    (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
    ∀ᶠj : ℕ in atTop,vectorExponentialGenerator (vectorExponentialLocalized j f) X d σ r sample=
      vectorExponentialGenerator f X d σ r sample := by
  filter_upwards [vectorExponentialLocalized_eventually_eq f r
    ⟨r.coe_nonneg,hr⟩ sample.1 (X r sample)] with j hj
  have hs := hj.comp_tendsto (show ContinuousAt
    (fun y : Field n=>((r:ℝ),(sample.1,y))) (X r sample) from by fun_prop)
  dsimp only [Function.comp_def] at hs
  have hfirst := hs.fderiv_eq (𝕜:=ℝ)
  have hsecond : vectorHessian (fun y=>vectorExponentialLocalized j f (r,(sample.1,y)))
      (X r sample)=vectorHessian (fun y=>f (r,(sample.1,y))) (X r sample):=
    (hs.fderiv (𝕜:=ℝ)).fderiv_eq
  have ht : vectorCompactSmoothTimeField (vectorExponentialLocalized j f)
      (r,(sample.1,X r sample))=vectorCompactSmoothTimeField f (r,(sample.1,X r sample)):=
    congrArg (fun L : VectorCompactTestParameter n→L[ℝ] ℝ=>L (1,(0,0))) (hj.fderiv_eq (𝕜:=ℝ))
  simp only [vectorExponentialGenerator,hfirst,hsecond,ht]

theorem vectorExponentialGenerator_bound
    (f : VectorCompactTestParameter n→ℝ)
    (X d : ℝ≥0→VectorDisorderBrownianSample n→Field n) (σ : ℝ)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n)
    (D B₁ B₂ Bₜ : ℝ) (hd : ‖d r sample‖≤D)
    (hfirst : ‖fderiv ℝ (fun y=>f (r,(sample.1,y))) (X r sample)‖≤B₁)
    (hsecond : ‖iteratedFDeriv ℝ 2 (fun y=>f (r,(sample.1,y))) (X r sample)‖≤B₂)
    (htime : ‖vectorCompactSmoothTimeField f (r,(sample.1,X r sample))‖≤Bₜ) :
    ‖vectorExponentialGenerator f X d σ r sample‖≤B₁*D+σ^2/2*((n:ℝ)*B₂)+Bₜ := by
  have hd0 : 0≤D:=(norm_nonneg _).trans hd
  have htrace : ‖vectorBilinearTrace
      (vectorHessian (fun y=>f (r,(sample.1,y))) (X r sample))‖≤(n:ℝ)*B₂ := by
    rw [Real.norm_eq_abs,vectorBilinearTrace]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑i : Fin n,B₂ := by
        apply Finset.sum_le_sum
        intro i _
        have hh:=vectorHessian_apply_bound
          (f:=fun y : Field n=>f (r,(sample.1,y))) (x:=X r sample) (K:=B₂)
          (by simpa only [vectorHessian_norm_eq] using hsecond)
          (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single i (1:ℝ))
        simpa only [PiLp.norm_single,norm_one,mul_one] using hh
      _ = _ := by simp
  unfold vectorExponentialGenerator
  apply (norm_add_le _ _).trans
  apply add_le_add _ htime
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact ((fderiv ℝ (fun y=>f (r,(sample.1,y))) (X r sample)).le_opNorm _).trans
      (mul_le_mul hfirst hd (norm_nonneg _) ((norm_nonneg _).trans hfirst))
  · rw [norm_mul,Real.norm_of_nonneg (div_nonneg (sq_nonneg σ) (by norm_num))]
    exact mul_le_mul_of_nonneg_left htrace (by positivity)

end QuantitativePaper
