module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterIntegralJets
public import FourPapersCommon.ExponentialDensityHessian

@[expose] public section

/-! Every evaluated positive log-density jet is a genuinely measurable bounded
random variable under the actual normalized outer posterior. This supplies
integrability before splitting the response into its individual groups. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ContDiff BigOperators
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

private theorem continuous_log_fixed_slice {A E F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : A×E→F) (hU : ContDiff ℝ ∞ U) (r : ℕ) (x : E) :
    Continuous (fun z : A=>iteratedFDeriv ℝ r (fun y=>U (z,y)) x) :=by
  exact (continuous_fieldSlice_iteratedFDeriv U hU r).comp
    (continuous_id.prodMk (continuous_const (y:=x)))

private theorem continuous_log_fixed_slice_apply {A E : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : A×E→ℝ) (hU : ContDiff ℝ ∞ U) (r : ℕ) (x : E) (b : Fin r→E) :
    Continuous (fun z : A=>iteratedFDeriv ℝ r (fun y=>U (z,y)) x b) :=by
  exact (continuous_eval_const b).comp (continuous_log_fixed_slice U hU r x)

private theorem measurable_finite_fixed_slice_jet {A E : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : S→E×A→ℝ) (hU : ∀σ, ContDiff ℝ ∞ (U σ))
    (r : ℕ) (x : E) (b : Fin r→E) :
    Measurable (fun p : A×S=>iteratedFDeriv ℝ r (fun Q=>U p.2 (Q,p.1)) x b) :=by
  apply measurable_from_prod_countable_left
  intro σ
  have hc:Continuous (fun z : A=>iteratedFDeriv ℝ r (fun Q=>U σ (Q,z)) x b):=
    continuous_log_fixed_slice_apply (fun p : A×E=>U σ (p.2,p.1))
      ((hU σ).comp (contDiff_snd.prodMk contDiff_fst)) r x b
  exact hc.measurable

set_option backward.isDefEq.respectTransparency true in
theorem measurable_cavityOuterPosterior_logJetApply
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N r : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (H : FiniteStateField S) (b : Fin r→FiniteStateField S) :
    Measurable (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
      iteratedFDeriv ℝ r (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H b) :=by
  let U:=fun σ (p : FiniteStateField S×(FiniteStateGaussianInput J×(Fin N→Field n)))=>
    cavityOuterPosteriorLogDensity V a L s N R p.1 (p.2.1,(p.2.2,σ))
  have hU:∀σ,ContDiff ℝ ∞ (U σ):=by
    intro σ
    exact contDiff_cavityOuterPosteriorLogDensity_joint V a ha L s N R σ
  have hm:=measurable_finite_fixed_slice_jet U hU r H b
  have he:Measurable (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
    ((p.1,p.2.1),p.2.2)):= (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  simpa only [U,Function.comp_def] using hm.comp he

theorem memLp_cavityOuterPosterior_logJetApply
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N r : ℕ) (hr : 1≤r)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (H : FiniteStateField S) (b : Fin r→FiniteStateField S) (q : ENNReal) :
    MemLp (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
      iteratedFDeriv ℝ r (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H b)
      q (cavityOuterPosteriorLaw V a L s N R H) :=by
  haveI:=cavityOuterPosteriorLaw_probability V a ha L s N R H
  obtain ⟨K,hK,hB⟩:=cavityOuterPosteriorLogDensity_bounded_positive_jets V a ha ha1 hdec L s N r R
  apply MemLp.of_bound (measurable_cavityOuterPosterior_logJetApply V a ha L s N r R H b).aestronglyMeasurable
    (K^r*∏i,‖b i‖)
  exact .of_forall fun p=>
    ((iteratedFDeriv ℝ r (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H).le_opNorm b).trans
      (mul_le_mul_of_nonneg_right (hB r hr le_rfl H p) (Finset.prod_nonneg (fun _ _=>norm_nonneg _)))

theorem memLp_cavityOuterPosterior_score
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (H K : FiniteStateField S) (q : ENNReal) :
    MemLp (fun p=>fderiv ℝ (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H K)
      q (cavityOuterPosteriorLaw V a L s N R H) :=by
  simpa only [iteratedFDeriv_one_apply] using
    memLp_cavityOuterPosterior_logJetApply V a ha ha1 hdec L s N 1 le_rfl R H (fun _=>K) q

theorem memLp_cavityOuterPosterior_secondScore
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (H K : FiniteStateField S) (q : ENNReal) :
    MemLp (fun p=>exponentialDensityHessian
      (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H K K)
      q (cavityOuterPosteriorLaw V a L s N R H) :=by
  simpa only [iteratedFDeriv_two_apply,exponentialDensityHessian] using
    memLp_cavityOuterPosterior_logJetApply V a ha ha1 hdec L s N 2 (by omega) R H (fun _=>K) q

theorem memLp_cavityOuterPosterior_fieldJetApply
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N r : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S)
    (H : FiniteStateField S) (b : Fin r→FiniteStateField S) (q : ENNReal) :
    MemLp (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
      iteratedFDeriv ℝ r f (H+R p.1+W p.2.1) b)
      q (cavityOuterPosteriorLaw V a L s N R H) :=by
  haveI:=cavityOuterPosteriorLaw_probability V a ha L s N R H
  obtain ⟨C,hC,hB⟩:=hf.2 r
  have hc:Continuous (fun Q : FiniteStateField S=>iteratedFDeriv ℝ r f Q b):=
    (continuous_eval_const b).comp (hf.1.continuous_iteratedFDeriv (by simp))
  have hm:Measurable (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>H+R p.1+W p.2.1):=by fun_prop
  apply MemLp.of_bound (hc.measurable.comp hm).aestronglyMeasurable (C*∏i,‖b i‖)
  exact .of_forall fun p=>
    ((iteratedFDeriv ℝ r f (H+R p.1+W p.2.1)).le_opNorm b).trans
      (mul_le_mul_of_nonneg_right (hB _) (Finset.prod_nonneg (fun _ _=>norm_nonneg _)))

theorem memLp_cavityOuterPosterior_fieldValue
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) (H : FiniteStateField S) (q : ENNReal) :
    MemLp (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>f (H+R p.1+W p.2.1))
      q (cavityOuterPosteriorLaw V a L s N R H) :=by
  simpa only [iteratedFDeriv_zero_apply] using
    memLp_cavityOuterPosterior_fieldJetApply V a ha L s N 0 R f hf W H Fin.elim0 q

end QuantitativeFollowup
