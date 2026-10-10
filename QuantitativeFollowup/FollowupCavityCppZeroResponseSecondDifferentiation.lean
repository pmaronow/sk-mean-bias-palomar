module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativePosteriorBounds

@[expose] public section

/-! Second differentiation of an observable under the genuine normalized
finite posterior. Both differentiations use the actual exponential density
and its proved derivative bounds. -/
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

theorem measurable_cascadePosterior_secondDifferential (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    Measurable (fun z : (Fin j→Field n)×S=>
      fderiv ℝ (fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L j Q z)) H) := by
  apply measurable_from_prod_countable_left
  intro σ
  let F:=fun z : (Fin j→Field n)×FiniteStateField S=>cascadePosteriorLogDensity V a L j z.2 (z.1,σ)
  let G:=fun z : (Fin j→Field n)×FiniteStateField S=>fderiv ℝ (fun Q=>F (z.1,Q)) z.2
  have hF : ContDiff ℝ ∞ F :=(contDiff_cascadePosteriorLogDensity V a ha L j σ).comp
    (contDiff_snd.prodMk contDiff_fst)
  have hG : ContDiff ℝ ∞ G :=contDiff_iff_contDiffAt.mpr fun z=>
    contDiffAt_partial_fderiv F z hF.contDiffAt
  have hd : Continuous (fun z : (Fin j→Field n)×FiniteStateField S=>
      fderiv ℝ (fun Q=>G (z.1,Q)) z.2) :=
    continuous_iff_continuousAt.mpr fun z=>(contDiffAt_partial_fderiv G z hG.contDiffAt).continuousAt
  exact (hd.comp (continuous_id.prodMk (continuous_const (y:=H)))).measurable

theorem hasFDerivAt_cascadePosteriorGaussianLaw_observable_directional_first
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
    HasFDerivAt
      (fun Q=>fderiv ℝ (fun R=>∫z,F R z∂cascadePosteriorGaussianLaw V a L j R) Q K)
      (∫z,fderiv ℝ (fun Q=>fderiv ℝ (fun R=>F R z) Q K+
          F Q z*(fderiv ℝ (fun R=>cascadePosteriorLogDensity V a L j R z) Q K)) H+
        (fderiv ℝ (fun R=>F R z) H K+
          F H z*(fderiv ℝ (fun R=>cascadePosteriorLogDensity V a L j R z) H K)) •
            fderiv ℝ (fun R=>cascadePosteriorLogDensity V a L j R z) H
        ∂cascadePosteriorGaussianLaw V a L j H) H := by
  let G:=fun Q z=>cascadePosteriorLogDensity V a L j Q z
  let DF:=fun Q z=>fderiv ℝ (fun R=>F R z) Q
  let DG:=fun Q z=>fderiv ℝ (fun R=>G R z) Q
  let Ψ:=fun Q z=>DF Q z K+F Q z*(DG Q z K)
  have hFD (z Q) : DifferentiableAt ℝ (fun R=>F R z) Q :=(hFC z).differentiable (by norm_num) Q
  have hDF (z) : ContDiff ℝ 1 (fun Q=>DF Q z) :=(hFC z).fderiv_right (by norm_num)
  have hG (z) : ContDiff ℝ ∞ (fun Q=>G Q z) :=
    (contDiff_cascadePosteriorLogDensity V a ha L j z.2).comp (contDiff_id.prodMk contDiff_const)
  have hDG (z) : ContDiff ℝ ∞ (fun Q=>DG Q z) :=(hG z).fderiv_right (by simp)
  have hDGb (Q z) : ‖DG Q z‖≤2 :=by
    rw [←norm_iteratedFDeriv_one]
    exact norm_cascadePosteriorLogDensity_firstJet_le_two V a ha ha1 hdec L j Q z
  have hDDGb (Q z) : ‖fderiv ℝ (fun R=>DG R z) Q‖≤1 :=by
    rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
    exact norm_cascadePosteriorLogDensity_secondJet_le_one V a ha ha1 hdec L j Q z
  have hΨm (Q) : Measurable (Ψ Q) :=
    ((ContinuousLinearMap.apply ℝ ℝ K).continuous.measurable.comp (hFDm Q)).add
      ((hFm Q).mul ((ContinuousLinearMap.apply ℝ ℝ K).continuous.measurable.comp
        (measurable_cascadePosterior_initialDifferential V a ha L j Q)))
  have hΨd (z Q) : DifferentiableAt ℝ (fun R=>Ψ R z) Q :=by
    exact (((hDF z).differentiable (by norm_num) Q).clm_apply (differentiableAt_const K)).add
      ((hFD z Q).mul (((hDG z).differentiable (by simp) Q).clm_apply (differentiableAt_const K)))
  have hΨjet (Q z) : fderiv ℝ (fun R=>Ψ R z) Q=
      ((ContinuousLinearMap.apply ℝ ℝ K).comp (fderiv ℝ (fun R=>DF R z) Q))+
      (DG Q z K) • DF Q z+F Q z •
        ((ContinuousLinearMap.apply ℝ ℝ K).comp (fderiv ℝ (fun R=>DG R z) Q)) :=by
    have hd1:=((hDF z).differentiable (by norm_num) Q).hasFDerivAt.clm_apply (hasFDerivAt_const K Q)
    have hd2:=((hDG z).differentiable (by simp) Q).hasFDerivAt.clm_apply (hasFDerivAt_const K Q)
    have hd:=(hd1.add ((hFD z Q).hasFDerivAt.mul hd2)).fderiv
    convert hd using 1 <;> (ext W; simp [Ψ,DF,DG]; ring)
  have hΨDm (Q) : Measurable (fun z=>fderiv ℝ (fun R=>Ψ R z) Q) :=by
    simp_rw [hΨjet]
    have hc : Continuous (fun T : FiniteStateField S→L[ℝ](FiniteStateField S→L[ℝ]ℝ)=>
      (ContinuousLinearMap.apply ℝ ℝ K).comp T) :=by fun_prop
    exact ((hc.measurable.comp (hFDDm Q)).add
      (((ContinuousLinearMap.apply ℝ ℝ K).continuous.measurable.comp
        (measurable_cascadePosterior_initialDifferential V a ha L j Q)).smul (hFDm Q))).add
      ((hFm Q).smul (hc.measurable.comp
        (measurable_cascadePosterior_secondDifferential V a ha L j Q)))
  have hΨb (Q z) : |Ψ Q z|≤(D+2*B)*‖K‖ :=by
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    have h1:=((DF Q z).le_opNorm K).trans (mul_le_mul_of_nonneg_right (hFDb Q z) (norm_nonneg K))
    have h2:=((DG Q z).le_opNorm K).trans (mul_le_mul_of_nonneg_right (hDGb Q z) (norm_nonneg K))
    simpa only [Real.norm_eq_abs,Ψ] using (add_le_add h1
      (mul_le_mul (hFb Q z) h2 (abs_nonneg _) hB)).trans_eq (by ring)
  have hΨDb (Q z) : ‖fderiv ℝ (fun R=>Ψ R z) Q‖≤(E+2*D+B)*‖K‖ :=by
    rw [hΨjet]
    apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    have hA : ‖(ContinuousLinearMap.apply ℝ ℝ K)‖≤‖K‖ :=by
      apply (ContinuousLinearMap.apply ℝ ℝ K).opNorm_le_bound (norm_nonneg K)
      intro T
      simpa only [ContinuousLinearMap.apply_apply,mul_comm] using T.le_opNorm K
    have h1:=(ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hA (hFDDb Q z) (norm_nonneg _) (norm_nonneg K))
    have h2:=mul_le_mul (((DG Q z).le_opNorm K).trans
      (mul_le_mul_of_nonneg_right (hDGb Q z) (norm_nonneg K))) (hFDb Q z) (norm_nonneg _) (by positivity)
    have h3:=mul_le_mul (hFb Q z)
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hA (hDDGb Q z) (norm_nonneg _) (norm_nonneg K))) (norm_nonneg _) hB
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
    exact (add_le_add (add_le_add h1 h2) h3).trans_eq (by ring)
  have hi:=hasFDerivAt_cascadePosteriorGaussianLaw_observable V a ha ha1 hdec L j Ψ
    hΨm hΨDm hΨd ((D+2*B)*‖K‖) ((E+2*D+B)*‖K‖)
    (by positivity) (by positivity) hΨb hΨDb H
  have he : (fun Q=>fderiv ℝ (fun R=>∫z,F R z∂cascadePosteriorGaussianLaw V a L j R) Q K)=
      fun Q=>∫z,Ψ Q z∂cascadePosteriorGaussianLaw V a L j Q :=by
    funext Q
    rw [(hasFDerivAt_cascadePosteriorGaussianLaw_observable V a ha ha1 hdec L j F
      hFm hFDm hFD B D hB hD hFb hFDb Q).fderiv]
    haveI:=cascadePosteriorGaussianLaw_probability V a ha L j Q
    have hm : Measurable (fun z=>DF Q z+F Q z • DG Q z) :=
      (hFDm Q).add ((hFm Q).smul (measurable_cascadePosterior_initialDifferential V a ha L j Q))
    have hb (z) : ‖DF Q z+F Q z • DG Q z‖≤D+2*B :=by
      apply (norm_add_le _ _).trans
      rw [norm_smul,Real.norm_eq_abs]
      exact (add_le_add (hFDb Q z) (mul_le_mul (hFb Q z) (hDGb Q z) (norm_nonneg _) hB)).trans_eq (by ring)
    rw [ContinuousLinearMap.integral_apply (Integrable.of_bound hm.aestronglyMeasurable _ (.of_forall hb))]
    rfl
  rw [he]
  exact hi

end QuantitativeFollowup
