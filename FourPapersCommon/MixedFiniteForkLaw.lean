module
public import FourPapersCommon.ParisiPhysicalForkLaw
public import FourPapersCommon.MixedFiniteRestrictedEndpoint
public import FourPapersCommon.MixedFiniteKernelConcatenation
public import FourPapersCommon.FiniteJointLaw
public import Mathlib.Probability.Kernel.CompProdEqIff

@[expose] public section

/-! The actual scalar Brownian fork has the genuine finite two-group
cascade endpoint law. Conditional-kernel uniqueness identifies the fresh
restart kernel almost everywhere under its real split-state distribution. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SpinGlass SpinGlass.Targets
open scoped NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1600000

theorem parisiPhysicalSplitState_mixed_apply (ξ : AdmissibleEvenMixture)
    (h : ℝ) (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : Paper.BrownianSample) :
    parisiPhysicalSplitState (mixedBeta ξ) h (mixedMeasure ξ μ) (ξ.unitClock q) sample=
      mixedState ξ h μ sample q :=
  parisiNoiseStatePath_canonical _ _ (mixedBeta_ne_zero ξ) _ _ _

theorem parisiPhysicalSplitState_mixed (ξ : AdmissibleEvenMixture)
    (h : ℝ) (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    parisiPhysicalSplitState (mixedBeta ξ) h (mixedMeasure ξ μ) (ξ.unitClock q)=
      fun sample=>mixedState ξ h μ sample q :=
  funext fun sample=>parisiPhysicalSplitState_mixed_apply ξ h μ q sample

theorem mixedFiniteForkState_law {k : ℕ} (ξ : AdmissibleEvenMixture)
    (h : ℝ) (s : RSBScheme k) (p n : ℕ) (hn : p+n≤k+2)
    (r q : Paper.Overlap) (hr : (r : ℝ)=s.q p) (hq : (q : ℝ)=s.q (p+n)) :
    brownianPairMeasure.map (fun sample=>(mixedState ξ h (Paper.parisiSchemeMeasure s) sample.1 q,
      mixedForkState ξ h (Paper.parisiSchemeMeasure s) r q sample))=
      mixedTwoGroupEndpointLaw ξ h s p n := by
  have hrq : (r : ℝ)≤q := by
    rw [hr,hq]
    exact s.q_mono' (p+n) hn p (by omega)
  let μ:=Paper.parisiSchemeMeasure s
  let a:=ξ.unitClock r
  let b:=ξ.unitClock q
  have hab : (a : ℝ)≤b := ξ.clock_strictMonoOn.monotoneOn r.property q.property hrq
  let K:=parisiPhysicalRestartKernel (mixedBeta ξ) (mixedMeasure ξ μ) a b hab
  let J:=mixedSchemeEndpointKernel ξ s p n
  let Y:=fun sample=>mixedState ξ h μ sample r
  let Z:=fun sample=>mixedState ξ h μ sample q
  let ν:=Paper.canonicalBrownianMeasure.map Y
  have hYa:=measurable_parisiPhysicalSplitState_past (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) a
  have hY : Measurable[Paper.canonicalBrownianFiltration (ξ.clock r).toNNReal] Y := by
    change Measurable[Paper.canonicalBrownianFiltration (ξ.clock r).toNNReal]
      (parisiPhysicalSplitState (mixedBeta ξ) h (mixedMeasure ξ μ) (ξ.unitClock r)) at hYa
    rw [parisiPhysicalSplitState_mixed] at hYa
    exact hYa
  have hYg : Measurable Y := hY.mono (Paper.canonicalBrownianFiltration.le _) le_rfl
  have hZ : Measurable Z := measurable_mixedState ξ h μ q.property
  letI : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hYg.aemeasurable).mpr inferInstance
  letI : IsMarkovKernel K := isMarkovKernel_parisiPhysicalRestartKernel _ (mixedBeta_ne_zero ξ) _ _ _ _
  letI : IsMarkovKernel J := isMarkovKernel_mixedSchemeEndpointKernel ξ s p n hn
  have hphysical : Paper.canonicalBrownianMeasure.map (fun sample=>(Y sample,Z sample))=ν ⊗ₘ K := by
    have he:=parisiPhysicalSplitState_joint_law (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) a b hab
    change Paper.canonicalBrownianMeasure.map (fun sample=>(
      parisiPhysicalSplitState (mixedBeta ξ) h (mixedMeasure ξ μ) (ξ.unitClock r) sample,
      parisiPhysicalSplitState (mixedBeta ξ) h (mixedMeasure ξ μ) (ξ.unitClock q) sample))=
      Paper.canonicalBrownianMeasure.map
        (parisiPhysicalSplitState (mixedBeta ξ) h (mixedMeasure ξ μ) (ξ.unitClock r)) ⊗ₘ K at he
    rw [parisiPhysicalSplitState_mixed,parisiPhysicalSplitState_mixed] at he
    exact he
  have hfinite : Paper.canonicalBrownianMeasure.map (fun sample=>(Y sample,Z sample))=ν ⊗ₘ J := by
    have hlaw : ∀E : Set Paper.BrownianSample,
        MeasurableSet[Paper.canonicalBrownianFiltration (ξ.clock r).toNNReal] E→
        (Paper.canonicalBrownianMeasure.restrict E).map Z=
          J ∘ₘ (Paper.canonicalBrownianMeasure.restrict E).map Y := by
      intro E hE
      rw [hr] at hE
      simpa only [Y,Z,J,μ,hr,hq] using
        mixedState_schemeEndpoint_restricted_transitionLaw ξ h s p n hn E hE
    have he:=joint_transitionLaw_of_restricted
      (Paper.canonicalBrownianFiltration (ξ.clock r).toNNReal) Paper.canonicalBrownianMeasure
      (Paper.canonicalBrownianFiltration.le _) Y hY Y Z hYg hZ id measurable_id
      (fun _=>rfl) J hlaw
    simpa only [Kernel.comap_id] using he
  have hKJ : K=ᵐ[ν] J := Kernel.ae_eq_of_compProd_eq (hphysical.symm.trans hfinite)
  have hfork : brownianPairMeasure.map (fun sample=>(mixedState ξ h μ sample.1 q,
      mixedForkState ξ h μ r q sample))=(K ×ₖ K) ∘ₘ ν := by
    have he:=parisiPhysicalForkState_joint_law (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) a b hab
    dsimp only [a,b] at he
    rw [parisiPhysicalSplitState_mixed,parisiPhysicalSplitState_mixed] at he
    exact he
  rw [hfork]
  have hprod : (K ×ₖ K) ∘ₘ ν=(J ×ₖ J) ∘ₘ ν := by
    apply Measure.comp_congr
    filter_upwards [hKJ] with x hx
    rw [Kernel.prod_apply,Kernel.prod_apply,hx]
  rw [hprod]
  unfold mixedTwoGroupEndpointLaw
  congr 1
  simpa only [ν,Y,μ,hr] using mixedState_schemeEndpoint_law ξ h s (p:=p) (by omega)

end FourPapersCommon
