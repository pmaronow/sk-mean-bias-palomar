module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativePosteriorBounds
public import FourPapersCommon.UniformDerivativeLimit

@[expose] public section

/-! Genuine uniform control of derivatives of finite posterior observables.
The posterior's changing law contributes through its actual score; bounds
on the observable's first two differentials yield one common modulus. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128

theorem cascadePosterior_observable_differential_lipschitz (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (F : FiniteStateField S→((Fin j→Field n)×S)→ℝ)
    (hFm : ∀Q,Measurable (F Q))
    (hFDm : ∀Q,Measurable (fun z=>fderiv ℝ (fun H=>F H z) Q))
    (hFD : ∀z Q,DifferentiableAt ℝ (fun H=>F H z) Q)
    (B D : ℝ) (C : ℝ≥0) (hB : 0≤B) (hD : 0≤D)
    (hFb : ∀Q z,|F Q z|≤B) (hFDb : ∀Q z,‖fderiv ℝ (fun H=>F H z) Q‖≤D)
    (hCL : ∀z,LipschitzWith C (fderiv ℝ (fun H=>F H z))) :
    LipschitzWith (C+4*D.toNNReal+5*B.toNNReal)
      (fderiv ℝ (fun Q=>∫z,F Q z∂cascadePosteriorGaussianLaw V a L j Q)) := by
  let P:=fun Q=>cascadePosteriorGaussianLaw V a L j Q
  let DF:=fun Q z=>fderiv ℝ (fun H=>F H z) Q
  let DL:=fun Q z=>fderiv ℝ (fun H=>cascadePosteriorLogDensity V a L j H z) Q
  let Ψ:=fun Q z=>DF Q z+F Q z • DL Q z
  have hPi (Q : FiniteStateField S) : IsProbabilityMeasure (P Q):=
    cascadePosteriorGaussianLaw_probability V a ha L j Q
  have hDLb (Q : FiniteStateField S) (z) : ‖DL Q z‖≤2 := by
    rw [←norm_iteratedFDeriv_one]
    exact norm_cascadePosteriorLogDensity_firstJet_le_two V a ha ha1 hdec L j Q z
  have hFL (z) : LipschitzWith D.toNNReal (fun Q=>F Q z) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (fun Q=>hFD z Q)
    intro Q
    rw [←NNReal.coe_le_coe,coe_nnnorm,Real.coe_toNNReal _ hD]
    exact hFDb Q z
  have hΨm (Q : FiniteStateField S) : Measurable (Ψ Q):=
    (hFDm Q).add ((hFm Q).smul (measurable_cascadePosterior_initialDifferential V a ha L j Q))
  have hΨb (Q : FiniteStateField S) (z) : ‖Ψ Q z‖≤D+2*B := by
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    have hh:=add_le_add (hFDb Q z) (mul_le_mul (hFb Q z) (hDLb Q z) (norm_nonneg _) hB)
    simpa only [mul_comm] using hh
  have hΨi (Q R : FiniteStateField S) : Integrable (Ψ Q) (P R) := by
    haveI:=hPi R
    exact Integrable.of_bound (hΨm Q).aestronglyMeasurable (D+2*B) (.of_forall (hΨb Q))
  have hΨdiff (Q H : FiniteStateField S) (z) :
      ‖Ψ Q z-Ψ H z‖≤(C+2*D+B)*‖Q-H‖ := by
    have he : Ψ Q z-Ψ H z=DF Q z-DF H z+
        (F Q z-F H z) • DL Q z+F H z • (DL Q z-DL H z) := by
      dsimp only [Ψ]
      module
    rw [he]
    apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
    have hc:=(hCL z).norm_sub_le Q H
    have hf:=(hFL z).norm_sub_le Q H
    have hl:=(cascadePosterior_logDifferential_lipschitz V a ha ha1 hdec L j z).norm_sub_le Q H
    simp only [Real.coe_toNNReal _ hD,Real.norm_eq_abs] at hf
    simp only [NNReal.coe_one,one_mul] at hl
    have h1 : |F Q z-F H z| * ‖DL Q z‖≤(D*‖Q-H‖)*2:=
      mul_le_mul hf (hDLb Q z) (norm_nonneg _) (by positivity)
    have h2 : |F H z| * ‖DL Q z-DL H z‖≤B*‖Q-H‖:=
      mul_le_mul (hFb H z) hl (norm_nonneg _) hB
    apply (add_le_add (add_le_add hc h1) h2).trans_eq
    ring
  have he (Q : FiniteStateField S) :
      fderiv ℝ (fun H=>∫z,F H z∂P H) Q=∫z,Ψ Q z∂P Q:=
    (hasFDerivAt_cascadePosteriorGaussianLaw_observable V a ha ha1 hdec L j F hFm hFDm hFD
      B D hB hD hFb hFDb Q).fderiv
  apply LipschitzWith.of_dist_le_mul
  intro Q H
  rw [dist_eq_norm,he,he]
  apply (∫z,Ψ Q z∂P Q-∫z,Ψ H z∂P H).opNorm_le_bound (by positivity)
  intro W
  rw [ContinuousLinearMap.sub_apply,ContinuousLinearMap.integral_apply (hΨi Q Q),
    ContinuousLinearMap.integral_apply (hΨi H H)]
  let f:=fun z=>Ψ H z W
  have hfm : Measurable f:=((ContinuousLinearMap.apply ℝ ℝ W).continuous.measurable.comp (hΨm H))
  have hfb (z) : |f z|≤(D+2*B)*‖W‖:=((Ψ H z).le_opNorm W).trans
    (mul_le_mul_of_nonneg_right (hΨb H z) (norm_nonneg W))
  have hLip:=(cascadePosterior_fixed_observable_lipschitz V a ha ha1 hdec L j f hfm
    ((D+2*B)*‖W‖) (by positivity) hfb).norm_sub_le Q H
  rw [Real.coe_toNNReal _ (by positivity)] at hLip
  haveI := hPi Q
  have hI : Integrable f (P Q) :=
    Integrable.of_bound hfm.aestronglyMeasurable ((D+2*B)*‖W‖) (.of_forall hfb)
  have hIq : Integrable (fun z=>Ψ Q z W) (P Q) := by
    apply Integrable.of_bound
      (((ContinuousLinearMap.apply ℝ ℝ W).continuous.measurable.comp (hΨm Q)).aestronglyMeasurable)
      ((D+2*B)*‖W‖)
    exact .of_forall (fun z => ((Ψ Q z).le_opNorm W).trans
      (mul_le_mul_of_nonneg_right (hΨb Q z) (norm_nonneg W)))
  have hdiff : ‖(∫z,Ψ Q z W∂P Q)-(∫z,Ψ H z W∂P Q)‖≤
      ((C+2*D+B)*‖Q-H‖)*‖W‖ := by
    haveI:=hPi Q
    rw [←integral_sub hIq hI]
    have hb (z) : ‖Ψ Q z W-Ψ H z W‖≤((C+2*D+B)*‖Q-H‖)*‖W‖ := by
      rw [←ContinuousLinearMap.sub_apply]
      exact ((Ψ Q z-Ψ H z).le_opNorm W).trans
        (mul_le_mul_of_nonneg_right (hΨdiff Q H z) (norm_nonneg W))
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := P Q) (.of_forall hb)
  have hh:=norm_sub_le_norm_sub_add_norm_sub
    (∫z,Ψ Q z W∂P Q) (∫z,Ψ H z W∂P Q) (∫z,Ψ H z W∂P H)
  apply (hh.trans (add_le_add hdiff hLip)).trans_eq
  simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,Real.coe_toNNReal _ hD,
    Real.coe_toNNReal _ hB,dist_eq_norm]
  ring

end QuantitativeFollowup
