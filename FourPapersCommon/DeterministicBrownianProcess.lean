module
public import FourPapersCommon.DeterministicBrownianIntegralVector
public import StochasticCalculus.ItoFormulaGeneral

@[expose] public section

/-! Deterministic stopping commutes with the genuine predictable embedding.
The resulting Wiener process has an actual continuous modification. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0→Ω→ℝ}
set_option maxHeartbeats 1000000

def deterministicTimeCut (f : Lp ℝ 2 nonnegativeLebesgueMeasure) (t : ℝ≥0) :
    Lp ℝ 2 nonnegativeLebesgueMeasure :=
  ((Lp.memLp f).indicator measurableSet_Ioc).toLp ((Ioc 0 t).indicator (f : ℝ≥0→ℝ))

theorem deterministicTimeCut_coeFn (f : Lp ℝ 2 nonnegativeLebesgueMeasure) (t : ℝ≥0) :
    (deterministicTimeCut f t : ℝ≥0→ℝ)=ᵐ[nonnegativeLebesgueMeasure]
      (Ioc 0 t).indicator (f : ℝ≥0→ℝ) :=
  ((Lp.memLp f).indicator measurableSet_Ioc).coeFn_toLp

theorem predictableTimeRestrict_deterministicEmbedding
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) (t : ℝ≥0) :
    predictableTimeRestrict 𝓕 t (deterministicPredictableEmbedding (P:=P) 𝓕 f)=
      deterministicPredictableEmbedding (P:=P) 𝓕 (deterministicTimeCut f t) := by
  apply Subtype.ext
  apply Lp.ext
  have hc : ∀ᵐp∂nonnegativeLebesgueMeasure.prod P,
      (deterministicTimeCut f t : ℝ≥0→ℝ) p.1=(Ioc 0 t).indicator (f : ℝ≥0→ℝ) p.1 :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (deterministicTimeCut_coeFn f t)
  filter_upwards [predictableTimeRestrict_coeFn 𝓕 t
    (deterministicPredictableEmbedding (P:=P) 𝓕 f),
    deterministicPredictableEmbedding_coeFn (P:=P) 𝓕 f,
    deterministicPredictableEmbedding_coeFn (P:=P) 𝓕 (deterministicTimeCut f t),hc]
    with p ht hf hcut hc
  rw [ht,hcut,Function.comp_apply,hc]
  by_cases hp : p.1∈Ioc 0 t
  · rw [indicator_of_mem (show p∈predictableTimeFrame (W:=Ω) t from ⟨hp,mem_univ _⟩),
      indicator_of_mem hp,hf,Function.comp_apply]
  · rw [indicator_of_notMem (show p∉predictableTimeFrame (W:=Ω) t from fun h=>hp h.1),
      indicator_of_notMem hp]

theorem naturalItoProcess_deterministic_eq_wiener
    (hB : IsPreBrownianReal B P) (hsm : ∀t,StronglyMeasurable (B t))
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (hnat : 𝓕=Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) (t : ℝ≥0) :
    naturalItoProcess hB hsm hnat (deterministicPredictableEmbedding (P:=P) 𝓕 f) t=
      wienerIntegral hB (deterministicTimeCut f t) := by
  unfold naturalItoProcess
  rw [predictableTimeRestrict_deterministicEmbedding]
  have he := congrArg (fun T : Lp ℝ 2 nonnegativeLebesgueMeasure→L[ℝ] RandomL2 P=>
    T (deterministicTimeCut f t)) (naturalItoIntegral_deterministic_eq_wiener hB hsm 𝓕 hnat)
  exact he

theorem exists_continuous_deterministicWiener_process
    (hB : IsBrownianMotion B P) (hsm : ∀t,StronglyMeasurable (B t))
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ∃Y : ℝ≥0→Ω→ℝ,
      (∀t,(wienerIntegral hB.toIsPreBrownianReal (deterministicTimeCut f t) : Ω→ℝ)=ᵐ[P]Y t) ∧
      ∀ᵐω∂P,Continuous (fun t=>Y t ω) := by
  obtain ⟨Y,hY⟩ := exists_continuousModification_naturalItoProcess hB hsm
    (deterministicPredictableEmbedding (P:=P) (Filtration.natural B hsm) f)
  refine ⟨Y,?_,hY.continuous_paths⟩
  intro t
  have he := naturalItoProcess_ae_eq_representative hB.toIsPreBrownianReal hsm rfl
    (deterministicPredictableEmbedding (P:=P) (Filtration.natural B hsm) f) t
  rw [naturalItoProcess_deterministic_eq_wiener hB.toIsPreBrownianReal hsm
    (Filtration.natural B hsm) rfl] at he
  exact he.trans (hY.fixedTime_ae_eq t)

end FourPapersCommon
