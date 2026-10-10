module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseSecondDifferentiation

@[expose] public section

/-! The literal second directional response of the true normalized posterior.
The moving observable contributes its genuine first and second derivatives;
the density contributes its actual log-score and log-Hessian. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem second_fderiv_cascadePosteriorGaussianLaw_observable
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (F : FiniteStateField S→((Fin j→Field n)×S)→ℝ)
    (hFm : ∀Q,Measurable (F Q))
    (hFDm : ∀Q,Measurable (fun z=>fderiv ℝ (fun H=>F H z) Q))
    (hFDDm : ∀Q,Measurable (fun z=>fderiv ℝ (fderiv ℝ (fun H=>F H z)) Q))
    (hFC : ∀z,ContDiff ℝ 2 (fun H=>F H z))
    (B D E : ℝ) (hB : 0≤B) (hD : 0≤D) (hE : 0≤E)
    (hFb : ∀Q z,|F Q z|≤B) (hFDb : ∀Q z,‖fderiv ℝ (fun H=>F H z) Q‖≤D)
    (hFDDb : ∀Q z,‖fderiv ℝ (fderiv ℝ (fun H=>F H z)) Q‖≤E)
    (H K : FiniteStateField S) :
    fderiv ℝ (fun Q=>fderiv ℝ
      (fun R=>∫z,F R z∂cascadePosteriorGaussianLaw V a L j R) Q K) H K =
    ∫z, fderiv ℝ (fun Q=>fderiv ℝ (fun R=>F R z) Q K) H K+
      2*(fderiv ℝ (fun R=>F R z) H K)*
        (fderiv ℝ (fun R=>cascadePosteriorLogDensity V a L j R z) H K)+
      F H z*((fderiv ℝ (fun R=>cascadePosteriorLogDensity V a L j R z) H K)^2+
        fderiv ℝ (fun Q=>fderiv ℝ
          (fun R=>cascadePosteriorLogDensity V a L j R z) Q K) H K)
      ∂cascadePosteriorGaussianLaw V a L j H := by
  let G:=fun Q z=>cascadePosteriorLogDensity V a L j Q z
  let DF:=fun Q z=>fderiv ℝ (fun R=>F R z) Q
  let DG:=fun Q z=>fderiv ℝ (fun R=>G R z) Q
  let Ψ:=fun Q z=>DF Q z K+F Q z*(DG Q z K)
  let A:=ContinuousLinearMap.apply ℝ ℝ K
  let I:=fun z=>fderiv ℝ (fun Q=>Ψ Q z) H+Ψ H z • DG H z
  have hDF (z) : ContDiff ℝ 1 (fun Q=>DF Q z) :=(hFC z).fderiv_right (by norm_num)
  have hG (z) : ContDiff ℝ ∞ (fun Q=>G Q z) :=
    (contDiff_cascadePosteriorLogDensity V a ha L j z.2).comp (contDiff_id.prodMk contDiff_const)
  have hDG (z) : ContDiff ℝ ∞ (fun Q=>DG Q z) :=(hG z).fderiv_right (by simp)
  have hjet (z) : fderiv ℝ (fun Q=>Ψ Q z) H=
      A.comp (fderiv ℝ (fun Q=>DF Q z) H)+(DG H z K) • DF H z+
      F H z • A.comp (fderiv ℝ (fun Q=>DG Q z) H) :=by
    have hd1:=((hDF z).differentiable (by norm_num) H).hasFDerivAt.clm_apply (hasFDerivAt_const K H)
    have hd2:=((hDG z).differentiable (by simp) H).hasFDerivAt.clm_apply (hasFDerivAt_const K H)
    have hd:=(hd1.add (((hFC z).differentiable (by norm_num) H).hasFDerivAt.mul hd2)).fderiv
    convert hd using 1 <;> (ext W; simp [Ψ,DF,DG,A]; ring)
  have hDGm : Measurable (DG H) :=measurable_cascadePosterior_initialDifferential V a ha L j H
  have hDDGm : Measurable (fun z=>fderiv ℝ (fun Q=>DG Q z) H) :=
    measurable_cascadePosterior_secondDifferential V a ha L j H
  have hc : Continuous (fun T : FiniteStateField S→L[ℝ](FiniteStateField S→L[ℝ]ℝ)=>A.comp T) :=by fun_prop
  have hIm : Measurable I :=by
    simp only [I,hjet]
    exact (((hc.measurable.comp (hFDDm H)).add
      ((A.continuous.measurable.comp hDGm).smul (hFDm H))).add
      ((hFm H).smul (hc.measurable.comp hDDGm))).add
      ((((A.continuous.measurable.comp (hFDm H)).add
        ((hFm H).mul (A.continuous.measurable.comp hDGm))).smul hDGm))
  have hAb : ‖A‖≤‖K‖ :=by
    apply A.opNorm_le_bound (norm_nonneg K)
    intro T
    simpa only [A,ContinuousLinearMap.apply_apply,mul_comm] using T.le_opNorm K
  have hGb (z) : ‖DG H z‖≤2 :=by
    rw [←norm_iteratedFDeriv_one]
    exact norm_cascadePosteriorLogDensity_firstJet_le_two V a ha ha1 hdec L j H z
  have hGGb (z) : ‖fderiv ℝ (fun Q=>DG Q z) H‖≤1 :=by
    rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
    exact norm_cascadePosteriorLogDensity_secondJet_le_one V a ha ha1 hdec L j H z
  have hΨb (z) : |Ψ H z|≤(D+2*B)*‖K‖ :=by
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    have h1:=((DF H z).le_opNorm K).trans (mul_le_mul_of_nonneg_right (hFDb H z) (norm_nonneg K))
    have h2:=((DG H z).le_opNorm K).trans (mul_le_mul_of_nonneg_right (hGb z) (norm_nonneg K))
    simpa only [Real.norm_eq_abs,Ψ] using (add_le_add h1
      (mul_le_mul (hFb H z) h2 (abs_nonneg _) hB)).trans_eq (by ring)
  have hIb (z) : ‖I z‖≤(E+4*D+5*B)*‖K‖ :=by
    dsimp only [I]
    rw [hjet]
    have h1:=(ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hAb (hFDDb H z) (norm_nonneg _) (norm_nonneg K))
    have h2:=mul_le_mul (((DG H z).le_opNorm K).trans
      (mul_le_mul_of_nonneg_right (hGb z) (norm_nonneg K))) (hFDb H z) (norm_nonneg _) (by positivity)
    have h3:=mul_le_mul (hFb H z)
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hAb (hGGb z) (norm_nonneg _) (norm_nonneg K))) (norm_nonneg _) hB
    have h4:=mul_le_mul (hΨb z) (hGb z) (norm_nonneg _) (by positivity)
    apply (norm_add_le _ _).trans
    apply (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl).trans
    rw [norm_smul,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs]
    exact (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans_eq (by ring)
  haveI:=cascadePosteriorGaussianLaw_probability V a ha L j H
  have hi : Integrable I (cascadePosteriorGaussianLaw V a L j H) :=
    Integrable.of_bound hIm.aestronglyMeasurable _ (.of_forall hIb)
  rw [(hasFDerivAt_cascadePosteriorGaussianLaw_observable_directional_first V a ha ha1 hdec L j F
    hFm hFDm hFDDm hFC B D E hB hD hE hFb hFDb hFDDb H K).fderiv]
  change (∫z,I z ∂cascadePosteriorGaussianLaw V a L j H) K=_
  rw [ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  exact .of_forall fun z=>by
    dsimp only [I]
    rw [hjet]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,smul_eq_mul]
    have heF : fderiv ℝ (fun Q=>DF Q z K) H K=
        (fderiv ℝ (fun Q=>DF Q z) H K) K :=by
      rw [(((hDF z).differentiable (by norm_num) H).hasFDerivAt.clm_apply
        (hasFDerivAt_const K H)).fderiv]
      simp
    have heG : fderiv ℝ (fun Q=>DG Q z K) H K=
        (fderiv ℝ (fun Q=>DG Q z) H K) K :=by
      rw [(((hDG z).differentiable (by simp) H).hasFDerivAt.clm_apply
        (hasFDerivAt_const K H)).fderiv]
      simp
    change _=fderiv ℝ (fun Q=>DF Q z K) H K+2*(DF H z K)*(DG H z K)+
      F H z*((DG H z K)^2+fderiv ℝ (fun Q=>DG Q z K) H K)
    rw [heF,heG]
    dsimp only [Ψ,A]
    simp only [ContinuousLinearMap.apply_apply]
    ring

end QuantitativeFollowup
