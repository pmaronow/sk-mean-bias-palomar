module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeFinite

@[expose] public section

/-! Depth-independent variation estimates for the actual normalized
remaining posterior. These follow from its genuine first and second
log-density derivatives, rather than an assumed total-variation bound. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem cascadePosterior_logDifferential_lipschitz (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (z : (Fin j→Field n)×S) :
    LipschitzWith 1 (fderiv ℝ (fun H=>cascadePosteriorLogDensity V a L j H z)) := by
  have hs:=((contDiff_cascadePosteriorLogDensity V a ha L j z.2).comp
    (contDiff_id.prodMk (contDiff_const (c:=z.1)))).fderiv_right (m:=∞) (by simp)
  apply lipschitzWith_of_nnnorm_fderiv_le (hs.differentiable (by simp))
  intro H
  rw [←NNReal.coe_le_coe,coe_nnnorm,←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
  exact norm_cascadePosteriorLogDensity_secondJet_le_one V a ha ha1 hdec L j H z

theorem hasFDerivAt_cascadePosterior_fixed_observable (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (f : ((Fin j→Field n)×S)→ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0≤B) (hb : ∀z,|f z|≤B) (H : FiniteStateField S) :
    HasFDerivAt (fun Q=>∫z,f z∂cascadePosteriorGaussianLaw V a L j Q)
      (∫z,f z • fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L j Q z) H
        ∂cascadePosteriorGaussianLaw V a L j H) H := by
  have hh:=hasFDerivAt_cascadePosteriorGaussianLaw_observable V a ha ha1 hdec L j
    (fun _ z=>f z) (fun _=>hf) (fun _=>by simp only [fderiv_const_apply];exact measurable_const)
    (fun _ _=>differentiableAt_const _) B 0 hB le_rfl (fun _ z=>hb z)
    (fun _ _=>by simp) H
  simpa only [fderiv_const_apply,zero_add] using hh

theorem cascadePosterior_fixed_observable_differential_bound (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (f : ((Fin j→Field n)×S)→ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0≤B) (hb : ∀z,|f z|≤B) (H : FiniteStateField S) :
    ‖fderiv ℝ (fun Q=>∫z,f z∂cascadePosteriorGaussianLaw V a L j Q) H‖≤2*B := by
  haveI:=cascadePosteriorGaussianLaw_probability V a ha L j H
  rw [(hasFDerivAt_cascadePosterior_fixed_observable V a ha ha1 hdec L j f hf B hB hb H).fderiv]
  have hbound : ∀z,‖f z • fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L j Q z) H‖≤2*B := by
    intro z
    rw [norm_smul,Real.norm_eq_abs]
    have hd : ‖fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L j Q z) H‖≤2 := by
      rw [←norm_iteratedFDeriv_one]
      exact norm_cascadePosteriorLogDensity_firstJet_le_two V a ha ha1 hdec L j H z
    simpa only [mul_comm] using mul_le_mul (hb z) hd (norm_nonneg _) hB
  simpa only [probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=cascadePosteriorGaussianLaw V a L j H) (.of_forall hbound)

theorem cascadePosterior_fixed_observable_lipschitz (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (f : ((Fin j→Field n)×S)→ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0≤B) (hb : ∀z,|f z|≤B) :
    LipschitzWith (2*B).toNNReal (fun Q=>∫z,f z∂cascadePosteriorGaussianLaw V a L j Q) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (fun H=>(hasFDerivAt_cascadePosterior_fixed_observable V a ha ha1 hdec L j f hf B hB hb H).differentiableAt)
  intro H
  rw [←NNReal.coe_le_coe,coe_nnnorm,Real.coe_toNNReal _ (by positivity)]
  exact cascadePosterior_fixed_observable_differential_bound V a ha ha1 hdec L j f hf B hB hb H

end QuantitativeFollowup
