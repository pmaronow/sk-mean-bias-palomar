module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeSquareBounds
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeUniform

@[expose] public section

/-! One depth-independent modulus for the true derivative of every retained
square posterior expectation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128

theorem cascadePosterior_retained_square_differential_lipschitz (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K : FiniteStateField S) :
    LipschitzWith (31*‖K‖₊^2)
      (fderiv ℝ (fun H=>∫z,cascadePosteriorRetainedSquare V a L j i K H z
        ∂cascadePosteriorGaussianLaw V a L j H)) := by
  let F:=cascadePosteriorRetainedSquare V a L j i K
  have hs : ContDiff ℝ ∞ (fun z : (Fin j→Field n)×FiniteStateField S=>
      F z.2 (z.1,Classical.choice inferInstance)) :=
    (contDiff_cascadePosteriorRetainedMean V a ha L j i K).pow 2
  have hFm (Q : FiniteStateField S) : Measurable (F Q) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact (hs.continuous.comp (continuous_id.prodMk continuous_const)).measurable
  have hFDm (Q : FiniteStateField S) : Measurable (fun z=>fderiv ℝ (fun H=>F H z) Q) := by
    apply measurable_from_prod_countable_left
    intro σ
    have hd : Continuous (fun z : (Fin j→Field n)×FiniteStateField S=>
        fderiv ℝ (fun H=>F H (z.1,Classical.choice inferInstance)) z.2) :=
      continuous_iff_continuousAt.mpr fun z=>
        (contDiffAt_partial_fderiv _ z hs.contDiffAt).continuousAt
    exact (hd.comp (continuous_id.prodMk (continuous_const (y:=Q)))).measurable
  have hFD (z : (Fin j→Field n)×S) (Q : FiniteStateField S) :
      DifferentiableAt ℝ (fun H=>F H z) Q :=
    (hs.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) Q
  have hFb (Q : FiniteStateField S) (z : (Fin j→Field n)×S) : |F Q z|≤‖K‖^2 := by
    simpa only [F,cascadePosteriorRetainedSquare,abs_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (cascadePosteriorRetainedMean_bound V a ha L j i K Q z) 2
  have hl := cascadePosterior_observable_differential_lipschitz V a ha ha1 hdec L j F
    hFm hFDm hFD (‖K‖^2) (2*‖K‖^2) (18*‖K‖₊^2) (by positivity) (by positivity)
    hFb (fun Q z=>cascadePosteriorRetainedSquare_differential_bound V a ha ha1 hdec L j i K Q z)
    (fun z=>cascadePosteriorRetainedSquare_differential_lipschitz V a ha ha1 hdec L j i K z)
  convert hl using 1
  apply NNReal.eq
  simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_pow,coe_nnnorm,
    Real.coe_toNNReal _ (by positivity : 0≤2*‖K‖^2),Real.coe_toNNReal _ (by positivity : 0≤‖K‖^2)]
  ring

end QuantitativeFollowup
