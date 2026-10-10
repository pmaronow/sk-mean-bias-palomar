module
public import QuantitativeFollowup.FollowupCavitySignedResponseFiniteScore
public import FourPapersCommon.LocalExponentialScoreIntegral
public import FourPapersCommon.PartialFDerivSmooth

@[expose] public section

/-! Honest initial-field differentiation of the normalized retained
finite Gaussian posterior. Bounds and domination follow from the actual
posterior density and its depth-independent logarithmic derivative. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem measurable_cascadePosterior_initialDifferential (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    Measurable (fun z : (Fin j→Field n)×S=>
      fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L j Q z) H) := by
  apply measurable_from_prod_countable_left
  intro σ
  let F:=fun z : (Fin j→Field n)×FiniteStateField S=>cascadePosteriorLogDensity V a L j z.2 (z.1,σ)
  have hF : ContDiff ℝ ∞ F :=(contDiff_cascadePosteriorLogDensity V a ha L j σ).comp
    (contDiff_snd.prodMk contDiff_fst)
  have hd : Continuous (fun z : (Fin j→Field n)×FiniteStateField S=>
      fderiv ℝ (fun Q=>F (z.1,Q)) z.2) := by
    exact continuous_iff_continuousAt.mpr fun z=>
      (contDiffAt_partial_fderiv F z hF.contDiffAt).continuousAt
  exact (hd.comp (continuous_id.prodMk (continuous_const (y:=H)))).measurable

theorem integral_cascadePosteriorGaussianLaw_exp (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ((Fin j→Field n)×S)→E) :
    (∫z,f z∂cascadePosteriorGaussianLaw V a L j H)=
      ∫z,Real.exp (cascadePosteriorLogDensity V a L j H z) • f z
        ∂cascadePosteriorGaussianBase S (Fin n) j := by
  rw [cascadePosteriorGaussianLaw_eq_exp_density V a ha L j H,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_cascadePosteriorLogDensity V a ha L j H).exp.ennreal_ofReal)
      (.of_forall fun _=>ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem hasFDerivAt_cascadePosteriorGaussianLaw_observable (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (F : FiniteStateField S→((Fin j→Field n)×S)→ℝ)
    (hFm : ∀Q,Measurable (F Q))
    (hFDm : ∀Q,Measurable (fun z=>fderiv ℝ (fun H=>F H z) Q))
    (hFD : ∀z Q,DifferentiableAt ℝ (fun H=>F H z) Q)
    (B D : ℝ) (hB : 0≤B) (hD : 0≤D)
    (hFb : ∀Q z,|F Q z|≤B) (hFDb : ∀Q z,‖fderiv ℝ (fun H=>F H z) Q‖≤D)
    (H : FiniteStateField S) :
    HasFDerivAt (fun Q=>∫z,F Q z∂cascadePosteriorGaussianLaw V a L j Q)
      (∫z,fderiv ℝ (fun Q=>F Q z) H+F H z •
        fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L j Q z) H
        ∂cascadePosteriorGaussianLaw V a L j H) H := by
  let G:=cascadePosteriorLogDensity V a L j
  have hGd (z : (Fin j→Field n)×S) (Q : FiniteStateField S) :
      HasFDerivAt (fun y=>G y z) (fderiv ℝ (fun y=>G y z) Q) Q:=by
    have hh:=(contDiff_cascadePosteriorLogDensity V a ha L j z.2).comp
      (contDiff_id.prodMk (contDiff_const (c:=z.1)))
    exact (hh.differentiable (by simp) Q).hasFDerivAt
  have hGb (z : (Fin j→Field n)×S) (Q : FiniteStateField S) :
      ‖fderiv ℝ (fun y=>G y z) Q‖≤2:=by
    rw [←norm_iteratedFDeriv_one]
    exact norm_cascadePosteriorLogDensity_firstJet_le_two V a ha ha1 hdec L j Q z
  have hh:=hasFDerivAt_local_exponential_score_integral
    (cascadePosteriorGaussianBase S (Fin n) j) G F
    (fun Q z=>fderiv ℝ (fun y=>G y z) Q) (fun Q z=>fderiv ℝ (fun y=>F y z) Q)
    H 1 2 B D (by norm_num) (by norm_num) hB hD
    (fun Q _=>(measurable_cascadePosteriorLogDensity V a ha L j Q).aestronglyMeasurable)
    (fun Q _=>(hFm Q).aestronglyMeasurable)
    (measurable_cascadePosterior_initialDifferential V a ha L j H).aestronglyMeasurable
    (hFDm H).aestronglyMeasurable
    (integrable_cascadePosterior_exp V a ha L j H)
    (fun z Q _=>by
      have hl:=(cascadePosteriorLogDensity_lipschitz V a ha ha1 hdec L j z).norm_sub_le Q H
      have hl' : |G Q z-G H z|≤2*‖Q-H‖ := by
        simpa only [G,Real.norm_eq_abs,NNReal.coe_ofNat] using hl
      exact (le_abs_self (G Q z-G H z)).trans hl')
    (fun z Q _=>hFb Q z) (fun z Q _=>hGb z Q) (fun z Q _=>hFDb Q z)
    (fun z Q _=>hGd z Q) (fun z Q _=>(hFD z Q).hasFDerivAt)
  have he : (fun Q=>∫z,F Q z∂cascadePosteriorGaussianLaw V a L j Q)=
      (fun Q=>∫z,Real.exp (G Q z)*F Q z∂cascadePosteriorGaussianBase S (Fin n) j):=by
    funext Q
    simpa only [smul_eq_mul] using integral_cascadePosteriorGaussianLaw_exp V a ha L j Q (F Q)
  rw [he,integral_cascadePosteriorGaussianLaw_exp V a ha L j H]
  exact hh.2

end QuantitativeFollowup
