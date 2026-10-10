module
public import FourPapersCommon.MixedFiniteForkLaw

@[expose] public section

/-! Kernel uniqueness for the actual finite endpoint and fresh Brownian
restart, under their genuine starting-node law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SpinGlass SpinGlass.Targets
open scoped NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1600000

theorem mixedSchemeEndpointKernel_eq_restart_ae {k : ℕ} (ξ : AdmissibleEvenMixture)
    (h : ℝ) (s : RSBScheme k) (p n : ℕ) (hn : p+n≤k+2)
    (r q : Paper.Overlap) (hr : (r : ℝ)=s.q p) (hq : (q : ℝ)=s.q (p+n)) :
    parisiPhysicalRestartKernel (mixedBeta ξ) (mixedMeasure ξ (Paper.parisiSchemeMeasure s))
      (ξ.unitClock r) (ξ.unitClock q)
      (ξ.clock_strictMonoOn.monotoneOn r.property q.property (by
        rw [hr,hq];exact s.q_mono' (p+n) hn p (by omega)))=ᵐ[
      Paper.canonicalBrownianMeasure.map (fun ω=>mixedState ξ h (Paper.parisiSchemeMeasure s) ω r)]
      mixedSchemeEndpointKernel ξ s p n := by
  have hrq : (r : ℝ)≤q:=by rw [hr,hq];exact s.q_mono' (p+n) hn p (by omega)
  let μ:=Paper.parisiSchemeMeasure s
  let a:=ξ.unitClock r
  let b:=ξ.unitClock q
  have hab : (a : ℝ)≤b:=ξ.clock_strictMonoOn.monotoneOn r.property q.property hrq
  let K:=parisiPhysicalRestartKernel (mixedBeta ξ) (mixedMeasure ξ μ) a b hab
  let J:=mixedSchemeEndpointKernel ξ s p n
  let Y:=fun ω=>mixedState ξ h μ ω r
  let Z:=fun ω=>mixedState ξ h μ ω q
  let ν:=Paper.canonicalBrownianMeasure.map Y
  have hY : Measurable[Paper.canonicalBrownianFiltration (ξ.clock r).toNNReal] Y := by
    have he:=measurable_parisiPhysicalSplitState_past (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) a
    change Measurable[Paper.canonicalBrownianFiltration (ξ.clock r).toNNReal]
      (parisiPhysicalSplitState (mixedBeta ξ) h (mixedMeasure ξ μ) (ξ.unitClock r)) at he
    rw [parisiPhysicalSplitState_mixed] at he
    exact he
  have hYm : Measurable Y:=hY.mono (Paper.canonicalBrownianFiltration.le _) le_rfl
  have hZm : Measurable Z:=measurable_mixedState ξ h μ q.property
  letI : IsProbabilityMeasure ν:=(Measure.isProbabilityMeasure_map_iff hYm.aemeasurable).mpr inferInstance
  letI : IsMarkovKernel K:=isMarkovKernel_parisiPhysicalRestartKernel _ (mixedBeta_ne_zero ξ) _ _ _ _
  letI : IsMarkovKernel J:=isMarkovKernel_mixedSchemeEndpointKernel ξ s p n hn
  have hp : Paper.canonicalBrownianMeasure.map (fun ω=>(Y ω,Z ω))=ν ⊗ₘ K := by
    have he:=parisiPhysicalSplitState_joint_law (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) a b hab
    dsimp only [a,b] at he
    rw [parisiPhysicalSplitState_mixed,parisiPhysicalSplitState_mixed] at he
    exact he
  have hf : Paper.canonicalBrownianMeasure.map (fun ω=>(Y ω,Z ω))=ν ⊗ₘ J := by
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
      (Paper.canonicalBrownianFiltration.le _) Y hY Y Z hYm hZm id measurable_id
      (fun _=>rfl) J hlaw
    simpa only [Kernel.comap_id] using he
  exact Kernel.ae_eq_of_compProd_eq (hp.symm.trans hf)

end FourPapersCommon
