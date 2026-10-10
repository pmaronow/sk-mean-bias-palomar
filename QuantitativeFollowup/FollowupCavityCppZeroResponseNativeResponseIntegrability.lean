module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeResponseIntegral

@[expose] public section

/-! Integrability survives the genuine whole-history pushforward to the
native independent endpoint. The actual five response terms are not split
under a Bochner integral until this transport is established. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem nativeIntegrable_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem integrable_cavityFixedRowRawResponseIntegrand (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (d : ℕ) (hd : d≤k+2) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeIntegrable_zero_mem
    Integrable (cavityFixedRowRawResponseIntegrand D s a d i)
      (cavityOuterPosteriorLaw (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) 0) :=by
  dsimp only
  exact (cavityFixedRowOuterResponseWithoutNormalizer_integrable_eq s n β ρ hβ hρ a d hd i).1.congr
    (.of_forall fun p=>(cavityFixedRowRawResponseIntegrand_eq_withoutNormalizer s n β ρ hβ hρ
      a d hd i p).symm)

theorem integrable_cavityFixedRowNativeFiniteResponseIntegrand (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (d : ℕ) (hd : d≤k+2) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeIntegrable_zero_mem
    Integrable (cavityFixedRowNativeFiniteResponseIntegrand D s a d hd i)
      (anisotropicMeasureSpinPathLaw D (Paper.parisiSchemeMeasure s) a) :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeIntegrable_zero_mem
  let P:=cavityOuterPosteriorLaw (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) 0
  let h:=cavityOuterHistoryMap (cavityFiniteEnergyInput D s) (k+2) (anisotropicRootEnergyMap D) 0
  let F:=cavityFixedRowHistoryRawResponse D s a d i
  let g:=fun p : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
    (cavitySchemeEnergyHistoryProjection D (cavityNativeSchemeHistory D s p.1),p.2)
  have hh:Measurable h:=measurable_cavityOuterHistoryMap _ _ _ _
  have hF:Measurable F:=measurable_cavityFixedRowHistoryRawResponse D s a d i
  have hg:Measurable g:=
    ((measurable_cavitySchemeEnergyHistoryProjection D).comp
      ((measurable_cavityNativeSchemeHistory D s).comp measurable_fst)).prodMk measurable_snd
  have hi:Integrable (F ∘ h) P:=by
    have hr:=integrable_cavityFixedRowRawResponseIntegrand s n β ρ hβ hρ a d hd i
    exact hr.congr (.of_forall fun p=>cavityFixedRowRawResponseIntegrand_eq_history D s a d hd i p)
  have hiMap:Integrable F (P.map h):=
    (integrable_map_measure hF.aestronglyMeasurable hh.aemeasurable).2 hi
  change Integrable F ((cavityOuterPosteriorLaw (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) 0).map
      (cavityOuterHistoryMap (cavityFiniteEnergyInput D s) (k+2) (anisotropicRootEnergyMap D) 0)) at hiMap
  rw [cavityOuterPosteriorHistory_eq_native_scheme D s a] at hiMap
  have hiNative:Integrable (F ∘ g) (anisotropicMeasureSpinPathLaw D (Paper.parisiSchemeMeasure s) a):=
    (integrable_map_measure hF.aestronglyMeasurable hg.aemeasurable).1 hiMap
  exact hiNative.congr (.of_forall fun p=>cavityFixedRowHistoryRawResponse_at_native D s a ha has hq d hd i p)

end QuantitativeFollowup
