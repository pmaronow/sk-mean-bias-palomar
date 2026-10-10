module
public import StochasticCalculus.ItoConstruction
public import StochasticCalculus.WienerIntegral

@[expose] public section

/-! The natural-filtration Itô integral agrees with the genuine Wiener
integral on every deterministic square-integrable time function. Equality
is proved on interval indicators and extended through their dense span. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open scoped NNReal
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0→Ω→ℝ}
set_option maxHeartbeats 1000000

theorem naturalItoIntegral_deterministic_eq_wiener
    (hB : IsPreBrownianReal B P) (hsm : ∀t,StronglyMeasurable (B t))
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (hnat : 𝓕=Filtration.natural B hsm) :
    (naturalItoIntegral hB hsm hnat).comp
      (deterministicPredictableEmbedding (P:=P) 𝓕).toContinuousLinearMap=
      wienerIntegral hB := by
  refine ContinuousLinearMap.ext_on dense_span_intervalIndicator ?_
  rintro _ ⟨t,rfl⟩
  change naturalItoIntegral hB hsm hnat
    (deterministicPredictableEmbedding (P:=P) 𝓕 (intervalIndicator t))=
      wienerIntegral hB (intervalIndicator t)
  rw [←elementaryPredictable_adaptedOne,wienerIntegral_intervalIndicator,
    naturalItoIntegral_elementaryPredictable hB hsm hnat (show (0:ℝ≥0)≤t from bot_le)]
  apply Lp.ext
  filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat
    (show (0:ℝ≥0)≤t from bot_le) (adaptedOne (P:=P) 𝓕 0),
    Lp.coeFn_const 2 P (1:ℝ),hB.eval_zero_ae_eq_zero,coeFn_brownianLp hB t]
    with ω hi h1 h0 ht
  change (adaptedOne (P:=P) 𝓕 0 : Ω→ℝ) ω=1 at h1
  rw [hi,h1,h0,ht,sub_zero,one_mul]

theorem hasGaussianLaw_naturalItoIntegral_deterministic
    (hB : IsPreBrownianReal B P) (hsm : ∀t,StronglyMeasurable (B t))
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (hnat : 𝓕=Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    HasGaussianLaw (naturalItoIntegral hB hsm hnat
      (deterministicPredictableEmbedding (P:=P) 𝓕 f) : Ω→ℝ) P := by
  have he := congrArg (fun T : Lp ℝ 2 nonnegativeLebesgueMeasure→L[ℝ] RandomL2 P=>T f)
    (naturalItoIntegral_deterministic_eq_wiener hB hsm 𝓕 hnat)
  change naturalItoIntegral hB hsm hnat (deterministicPredictableEmbedding (P:=P) 𝓕 f)=
    wienerIntegral hB f at he
  rw [he]
  exact hasGaussianLaw_wienerIntegral hB f

theorem map_naturalItoIntegral_deterministic_eq_gaussianReal
    (hB : IsPreBrownianReal B P) (hsm : ∀t,StronglyMeasurable (B t))
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (hnat : 𝓕=Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    P.map (naturalItoIntegral hB hsm hnat
      (deterministicPredictableEmbedding (P:=P) 𝓕 f))=gaussianReal 0 (‖f‖₊^2) := by
  have he := congrArg (fun T : Lp ℝ 2 nonnegativeLebesgueMeasure→L[ℝ] RandomL2 P=>T f)
    (naturalItoIntegral_deterministic_eq_wiener hB hsm 𝓕 hnat)
  change naturalItoIntegral hB hsm hnat (deterministicPredictableEmbedding (P:=P) 𝓕 f)=
    wienerIntegral hB f at he
  rw [he]
  exact map_wienerIntegral_eq_gaussianReal hB f

end FourPapersCommon
