module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseObservableData
public import FourPapersCommon.FiniteCascadeTreeGaussianDensity

@[expose] public section

/-! The genuine outer Gaussian tilt together with the entire normalized
retained posterior. Root and auxiliary Gaussian spaces may have different
dimensions. The reference law and its normalization are constructed here. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ENNReal NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

local instance cavityPosteriorGaussianBase_finite (N : ℕ) :
    IsFiniteMeasure (cascadePosteriorGaussianBase S (Fin n) N) :=by
  unfold cascadePosteriorGaussianBase
  infer_instance

theorem measurable_cascadePosteriorLogDensity_joint (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ) :
    Measurable (fun p : FiniteStateField S×((Fin N→Field n)×S)=>
      cascadePosteriorLogDensity V a L N p.1 p.2) :=by
  have hm : Measurable (fun p : (FiniteStateField S×(Fin N→Field n))×S=>
      cascadePosteriorLogDensity V a L N p.1.1 (p.1.2,p.2)) :=
    measurable_from_prod_countable_left fun σ=>(contDiff_cascadePosteriorLogDensity V a ha L N σ).continuous.measurable
  exact hm.comp (show Measurable (fun p : FiniteStateField S×((Fin N→Field n)×S)=>
    ((p.1,p.2.1),p.2.2)) from by fun_prop)

def cavityPosteriorGaussianKernel (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ) :
    Kernel (FiniteStateField S) ((Fin N→Field n)×S) :=
  (Kernel.const (FiniteStateField S) (cascadePosteriorGaussianBase S (Fin n) N)).withDensity
    (fun H z=>ENNReal.ofReal (Real.exp (cascadePosteriorLogDensity V a L N H z)))

theorem cavityPosteriorGaussianKernel_apply (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ)
    (H : FiniteStateField S) :
    cavityPosteriorGaussianKernel V a L N H=cascadePosteriorGaussianLaw V a L N H :=by
  rw [cavityPosteriorGaussianKernel,Kernel.withDensity_apply _
    (measurable_cascadePosteriorLogDensity_joint V a ha L N).exp.ennreal_ofReal,Kernel.const_apply]
  exact (cascadePosteriorGaussianLaw_eq_exp_density V a ha L N H).symm

theorem cavityPosteriorGaussianKernel_markov (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ) :
    IsMarkovKernel (cavityPosteriorGaussianKernel V a L N) :=by
  constructor
  intro H
  rw [cavityPosteriorGaussianKernel_apply V a ha L N H]
  exact cascadePosteriorGaussianLaw_probability V a ha L N H

def cavityOuterPosteriorNormalizer (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) : ℝ :=
  finiteCascadeTreeGaussianNormalizer V a L s N R H

theorem cavityOuterPosteriorNormalizer_eq_integral (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    cavityOuterPosteriorNormalizer V a L s N R H=
      ∫g,Real.exp (s*finiteStateGaussianTerminalCascade V a L N (H+R g))
        ∂stdGaussian (FiniteStateGaussianInput J) :=by
  rw [cavityOuterPosteriorNormalizer,finiteCascadeTreeGaussianNormalizer,
    finiteStateGaussianRawKernel_apply,integral_map (by fun_prop)
      (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L N).continuous.measurable.const_mul s).exp.aestronglyMeasurable)]

def cavityOuterPosteriorLaw (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :=
  ((stdGaussian (FiniteStateGaussianInput J)).tilted
    (fun g=>s*finiteStateGaussianTerminalCascade V a L N (H+R g))) ⊗ₘ
    (cavityPosteriorGaussianKernel V a L N).comap (fun g=>H+R g) (by fun_prop)

theorem cavityOuterPosteriorLaw_probability (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    IsProbabilityMeasure (cavityOuterPosteriorLaw V a L s N R H) :=by
  haveI:=cavityPosteriorGaussianKernel_markov V a ha L N
  haveI:=isProbabilityMeasure_tilted (integrable_exp_finiteStateGaussian_lipschitz
    (finiteStateGaussianTerminalCascade V a L N) (finiteStateGaussianTerminalCascade_lipschitz V a ha L N) R H s)
  unfold cavityOuterPosteriorLaw
  infer_instance

def cavityOuterPosteriorLogDensity (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (p : FiniteStateGaussianInput J×((Fin N→Field n)×S)) : ℝ :=
  s*finiteStateGaussianTerminalCascade V a L N (H+R p.1)+
    cascadePosteriorLogDensity V a L N (H+R p.1) p.2-
    Real.log (cavityOuterPosteriorNormalizer V a L s N R H)

theorem measurable_cavityOuterPosteriorLogDensity (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    Measurable (cavityOuterPosteriorLogDensity V a L s N R H) :=by
  exact ((((contDiff_one_finiteStateGaussianTerminalCascade V a ha L N).continuous.measurable.comp
    (measurable_const.add (R.measurable.comp measurable_fst))).const_mul s).add
    ((measurable_cascadePosteriorLogDensity_joint V a ha L N).comp
      (show Measurable (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
        (H+R p.1,p.2)) from by fun_prop))).sub_const _

theorem cavityOuterPosteriorLaw_eq_exp_density (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    cavityOuterPosteriorLaw V a L s N R H=
      ((stdGaussian (FiniteStateGaussianInput J)).prod (cascadePosteriorGaussianBase S (Fin n) N)).withDensity
        (fun p=>ENNReal.ofReal (Real.exp (cavityOuterPosteriorLogDensity V a L s N R H p))) :=by
  let Z:=cavityOuterPosteriorNormalizer V a L s N R H
  have hZ : 0<Z:=finiteCascadeTreeGaussianNormalizer_pos V a ha L s N R H
  let w:=fun g (z : (Fin N→Field n)×S)=>ENNReal.ofReal
    (Real.exp (cascadePosteriorLogDensity V a L N (H+R g) z))
  have hw : Measurable (Function.uncurry w):=
    ((measurable_cascadePosteriorLogDensity_joint V a ha L N).comp
      (show Measurable (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
        (H+R p.1,p.2)) from by fun_prop)).exp.ennreal_ofReal
  have hk : (cavityPosteriorGaussianKernel V a L N).comap (fun g=>H+R g) (by fun_prop)=
      (Kernel.const (FiniteStateGaussianInput J) (cascadePosteriorGaussianBase S (Fin n) N)).withDensity w :=by
    ext g : 1
    rw [Kernel.comap_apply,cavityPosteriorGaussianKernel_apply V a ha L N,
      Kernel.withDensity_apply _ hw,Kernel.const_apply,cascadePosteriorGaussianLaw_eq_exp_density V a ha L N]
  haveI:=cavityPosteriorGaussianKernel_markov V a ha L N
  haveI : IsSFiniteKernel ((Kernel.const (FiniteStateGaussianInput J)
      (cascadePosteriorGaussianBase S (Fin n) N)).withDensity w) :=by rw [←hk];infer_instance
  have hf : Measurable (fun g=>ENNReal.ofReal
      (Real.exp (s*finiteStateGaussianTerminalCascade V a L N (H+R g))/Z)) :=
    ((((contDiff_one_finiteStateGaussianTerminalCascade V a ha L N).continuous.measurable.comp
      (measurable_const.add R.measurable)).const_mul s).exp.div_const Z).ennreal_ofReal
  unfold cavityOuterPosteriorLaw Measure.tilted
  rw [hk,←cavityOuterPosteriorNormalizer_eq_integral V a ha L s N R H,
    Measure.withDensity_compProd_withDensity hf hw,Measure.compProd_const]
  congr 1
  funext p
  rw [←ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hZ.le)]
  congr 1
  dsimp only [w,cavityOuterPosteriorLogDensity]
  rw [Real.exp_sub,Real.exp_add,Real.exp_log hZ]
  ring

theorem lintegral_cavityOuterPosterior_exp (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    (∫⁻p,ENNReal.ofReal (Real.exp (cavityOuterPosteriorLogDensity V a L s N R H p))
      ∂(stdGaussian (FiniteStateGaussianInput J)).prod (cascadePosteriorGaussianBase S (Fin n) N))=1 :=by
  haveI:=cavityOuterPosteriorLaw_probability V a ha L s N R H
  have hh:=measure_univ (μ:=cavityOuterPosteriorLaw V a L s N R H)
  rw [cavityOuterPosteriorLaw_eq_exp_density V a ha L s N R H,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hh
  exact hh

theorem integrable_cavityOuterPosterior_exp (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    Integrable (fun p=>Real.exp (cavityOuterPosteriorLogDensity V a L s N R H p))
      ((stdGaussian (FiniteStateGaussianInput J)).prod (cascadePosteriorGaussianBase S (Fin n) N)) :=by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_cavityOuterPosteriorLogDensity V a ha L s N R H).exp.aestronglyMeasurable)
    (.of_forall fun _=>(Real.exp_pos _).le)).mp
  rw [lintegral_cavityOuterPosterior_exp V a ha L s N R H]
  exact ENNReal.one_ne_top

theorem integral_cavityOuterPosterior_exp (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    (∫p,Real.exp (cavityOuterPosteriorLogDensity V a L s N R H p)
      ∂(stdGaussian (FiniteStateGaussianInput J)).prod (cascadePosteriorGaussianBase S (Fin n) N))=1 :=by
  have hh:=ofReal_integral_eq_lintegral_ofReal (integrable_cavityOuterPosterior_exp V a ha L s N R H)
    (.of_forall fun _=>(Real.exp_pos _).le)
  rw [lintegral_cavityOuterPosterior_exp V a ha L s N R H] at hh
  have hn:=integral_nonneg (μ:=(stdGaussian (FiniteStateGaussianInput J)).prod
    (cascadePosteriorGaussianBase S (Fin n) N))
    (f:=fun p=>Real.exp (cavityOuterPosteriorLogDensity V a L s N R H p))
    (fun _=>(Real.exp_pos _).le)
  simpa only [ENNReal.toReal_ofReal hn,ENNReal.toReal_one] using congrArg ENNReal.toReal hh

theorem integral_cavityOuterPosteriorLaw_exp (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : FiniteStateGaussianInput J×((Fin N→Field n)×S)→E) :
    (∫p,f p∂cavityOuterPosteriorLaw V a L s N R H)=
      ∫p,Real.exp (cavityOuterPosteriorLogDensity V a L s N R H p) • f p
        ∂(stdGaussian (FiniteStateGaussianInput J)).prod (cascadePosteriorGaussianBase S (Fin n) N) :=by
  rw [cavityOuterPosteriorLaw_eq_exp_density V a ha L s N R H,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_cavityOuterPosteriorLogDensity V a ha L s N R H).exp.ennreal_ofReal)
      (.of_forall fun _=>ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le]

end QuantitativeFollowup
