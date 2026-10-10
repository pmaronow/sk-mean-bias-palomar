module
public import HexagonPaper.PathHeatContinuousSignedSource
public import HexagonPaper.PathHeatMomentContinuity

@[expose] public section

/-! Normalized moments for sources continuous in the active coordinates and
parameter with the auxiliary sample fixed. The auxiliary type has no topology.
Actual common-sample domination and measurability supply integration; no
normalized moment, normalizer or response continuity is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Z X Aux Ω : Type*} [TopologicalSpace Z]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [CompactSpace X] [SecondCountableTopology X]

 def pathHeatSectionWeight (d : Aux→PathHeatContinuousSignedSource (Z×C(X,ℝ)) X)
    (aux : Ω→Aux) (p : Z→Ω→C(X,ℝ)) (z : Z) (ω : Ω) : ℝ :=
  (d (aux ω)).weight (z,p z ω)

 def pathHeatSectionObservable (d : Aux→PathHeatContinuousSignedSource (Z×C(X,ℝ)) X)
    (aux : Ω→Aux) (p : Z→Ω→C(X,ℝ)) (z : Z) (ω : Ω) : ℝ :=
  (d (aux ω)).phi (z,p z ω)

 def pathHeatSectionDensityGenerator (d : Aux→PathHeatContinuousSignedSource (Z×C(X,ℝ)) X)
    (aux : Ω→Aux) (p : Z→Ω→C(X,ℝ)) (K : Z→X×X→ᵇℝ) (z : Z) (ω : Ω) : ℝ :=
  (d (aux ω)).densityGenerator (K z) (z,p z ω)

 def pathHeatSectionObservableGenerator (d : Aux→PathHeatContinuousSignedSource (Z×C(X,ℝ)) X)
    (aux : Ω→Aux) (p : Z→Ω→C(X,ℝ)) (K : Z→X×X→ᵇℝ) (z : Z) (ω : Ω) : ℝ :=
  (d (aux ω)).observableGenerator (K z) (z,p z ω)

 theorem pathHeat_sections_pointwiseContinuous
    (d : Aux→PathHeatContinuousSignedSource (Z×C(X,ℝ)) X)
    (aux : Ω→Aux) (p : Z→Ω→C(X,ℝ)) (K : Z→X×X→ᵇℝ)
    (ω : Ω) (hp : Continuous (fun z=>p z ω)) (hK : Continuous K) :
    Continuous (fun z=>pathHeatSectionWeight d aux p z ω) ∧
    Continuous (fun z=>pathHeatSectionObservable d aux p z ω) ∧
    Continuous (fun z=>pathHeatSectionDensityGenerator d aux p K z ω) ∧
    Continuous (fun z=>pathHeatSectionObservableGenerator d aux p K z ω) := by
  have hu : Continuous (fun z : Z=>(z,p z ω)) := continuous_id.prodMk hp
  refine ⟨(d (aux ω)).continuous_weight.comp hu,
    (d (aux ω)).continuous_phi.comp hu,?_,?_⟩
  · exact continuous_iff_continuousAt.mpr fun z=>
      (d (aux ω)).tendsto_densityGenerator (fun y=>(y,p y ω)) (z,p z ω)
        K (K z) hu.continuousAt.tendsto hK.continuousAt.tendsto
  · exact continuous_iff_continuousAt.mpr fun z=>
      (d (aux ω)).tendsto_observableGenerator (fun y=>(y,p y ω)) (z,p z ω)
        K (K z) hu.continuousAt.tendsto hK.continuousAt.tendsto

 theorem pathHeat_sections_normalized_continuity
    [FirstCountableTopology Z] [Nonempty Z] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Aux→PathHeatContinuousSignedSource (Z×C(X,ℝ)) X)
    (aux : Ω→Aux) (p : Z→Ω→C(X,ℝ)) (K : Z→X×X→ᵇℝ)
    (e : Ω→ℝ) (B C D : ℝ)
    (h : ∀z,PathHeatDominatedData μ (pathHeatSectionWeight d aux p z)
      (pathHeatSectionObservable d aux p z) (pathHeatSectionDensityGenerator d aux p K z)
      (pathHeatSectionObservableGenerator d aux p K z) e B C D)
    (hp : ∀ᵐω ∂μ,Continuous (fun z=>p z ω)) (hK : Continuous K) :
    (∀z,0<pathHeatNormalizer μ (pathHeatSectionWeight d aux p z)) ∧
    Continuous (fun z=>pathHeatNormalizer μ (pathHeatSectionWeight d aux p z)) ∧
    Continuous (fun z=>pathHeatExpectation μ (pathHeatSectionWeight d aux p z)
      (pathHeatSectionObservable d aux p z)) ∧
    Continuous (fun z=>pathHeatResponse μ (pathHeatSectionWeight d aux p z)
      (pathHeatSectionObservable d aux p z) (pathHeatSectionDensityGenerator d aux p K z)
      (pathHeatSectionObservableGenerator d aux p K z)) ∧
    Continuous (fun z=>pathHeatExpectation μ (pathHeatSectionWeight d aux p z)
      (pathHeatSectionDensityGenerator d aux p K z)) := by
  have hW := hp.mono fun ω hc=>(pathHeat_sections_pointwiseContinuous d aux p K ω hc hK).1
  have hF := hp.mono fun ω hc=>(pathHeat_sections_pointwiseContinuous d aux p K ω hc hK).2.1
  have hH := hp.mono fun ω hc=>(pathHeat_sections_pointwiseContinuous d aux p K ω hc hK).2.2.1
  have hJ := hp.mono fun ω hc=>(pathHeat_sections_pointwiseContinuous d aux p K ω hc hK).2.2.2
  have ht := continuous_pathHeat_normalized_moments
    (pathHeatSectionWeight d aux p) (pathHeatSectionObservable d aux p)
    (pathHeatSectionDensityGenerator d aux p K) (pathHeatSectionObservableGenerator d aux p K)
    e B C D h hW hF hH hJ
  have hIH := continuous_pathHeat_density_expectation
    (pathHeatSectionWeight d aux p) (pathHeatSectionObservable d aux p)
    (pathHeatSectionDensityGenerator d aux p K) (pathHeatSectionObservableGenerator d aux p K)
    e B C D h hW hH
  exact ⟨fun z=>pathHeat_normalizer_positive (h z),ht.1,ht.2.1,ht.2.2,hIH⟩

 theorem pathHeat_sections_movingValues {A : Type*} {l : Filter A}
    (d : Aux→PathHeatContinuousSignedSource (Z×C(X,ℝ)) X)
    (aux : Ω→Aux) (z : A→Z) (z₀ : Z) (p : A→Ω→C(X,ℝ)) (p₀ : Ω→C(X,ℝ))
    (K : A→X×X→ᵇℝ) (K₀ : X×X→ᵇℝ) (ω : Ω)
    (hz : Tendsto z l (𝓝 z₀)) (hp : Tendsto (fun i=>p i ω) l (𝓝 (p₀ ω)))
    (hK : Tendsto K l (𝓝 K₀)) :
    Tendsto (fun i=>(d (aux ω)).weight (z i,p i ω)) l
      (𝓝 ((d (aux ω)).weight (z₀,p₀ ω))) ∧
    Tendsto (fun i=>(d (aux ω)).phi (z i,p i ω)) l
      (𝓝 ((d (aux ω)).phi (z₀,p₀ ω))) ∧
    Tendsto (fun i=>(d (aux ω)).densityGenerator (K i) (z i,p i ω)) l
      (𝓝 ((d (aux ω)).densityGenerator K₀ (z₀,p₀ ω))) ∧
    Tendsto (fun i=>(d (aux ω)).observableGenerator (K i) (z i,p i ω)) l
      (𝓝 ((d (aux ω)).observableGenerator K₀ (z₀,p₀ ω))) :=
  (d (aux ω)).moving_values (fun i=>(z i,p i ω)) (z₀,p₀ ω) K K₀
    (hz.prodMk_nhds hp) hK

 theorem pathHeat_sections_moving_normalized_limits [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Aux→PathHeatContinuousSignedSource (Z×C(X,ℝ)) X)
    (aux : Ω→Aux) (z : ℕ→Z) (z₀ : Z) (p : ℕ→Ω→C(X,ℝ)) (p₀ : Ω→C(X,ℝ))
    (K : ℕ→X×X→ᵇℝ) (K₀ : X×X→ᵇℝ)
    (e : Ω→ℝ) (B C D : ℝ)
    (hn : ∀i,PathHeatDominatedData μ
      (fun ω=>(d (aux ω)).weight (z i,p i ω))
      (fun ω=>(d (aux ω)).phi (z i,p i ω))
      (fun ω=>(d (aux ω)).densityGenerator (K i) (z i,p i ω))
      (fun ω=>(d (aux ω)).observableGenerator (K i) (z i,p i ω)) e B C D)
    (h : PathHeatDominatedData μ
      (fun ω=>(d (aux ω)).weight (z₀,p₀ ω))
      (fun ω=>(d (aux ω)).phi (z₀,p₀ ω))
      (fun ω=>(d (aux ω)).densityGenerator K₀ (z₀,p₀ ω))
      (fun ω=>(d (aux ω)).observableGenerator K₀ (z₀,p₀ ω)) e B C D)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hp : ∀ᵐω ∂μ,Tendsto (fun i=>p i ω) atTop (𝓝 (p₀ ω)))
    (hK : Tendsto K atTop (𝓝 K₀)) :
    let W i ω := (d (aux ω)).weight (z i,p i ω)
    let F i ω := (d (aux ω)).phi (z i,p i ω)
    let H i ω := (d (aux ω)).densityGenerator (K i) (z i,p i ω)
    let J i ω := (d (aux ω)).observableGenerator (K i) (z i,p i ω)
    let W₀ ω := (d (aux ω)).weight (z₀,p₀ ω)
    let F₀ ω := (d (aux ω)).phi (z₀,p₀ ω)
    let H₀ ω := (d (aux ω)).densityGenerator K₀ (z₀,p₀ ω)
    let J₀ ω := (d (aux ω)).observableGenerator K₀ (z₀,p₀ ω)
    0<pathHeatNormalizer μ W₀ ∧
    Tendsto (fun i=>pathHeatNormalizer μ (W i)) atTop (𝓝 (pathHeatNormalizer μ W₀)) ∧
    Tendsto (fun i=>pathHeatExpectation μ (W i) (F i)) atTop
      (𝓝 (pathHeatExpectation μ W₀ F₀)) ∧
    Tendsto (fun i=>pathHeatResponse μ (W i) (F i) (H i) (J i)) atTop
      (𝓝 (pathHeatResponse μ W₀ F₀ H₀ J₀)) ∧
    Tendsto (fun i=>pathHeatExpectation μ (W i) (H i)) atTop
      (𝓝 (pathHeatExpectation μ W₀ H₀)) := by
  dsimp only
  have hW := hp.mono fun ω hc=>(pathHeat_sections_movingValues d aux z z₀ p p₀ K K₀ ω hz hc hK).1
  have hF := hp.mono fun ω hc=>(pathHeat_sections_movingValues d aux z z₀ p p₀ K K₀ ω hz hc hK).2.1
  have hH := hp.mono fun ω hc=>(pathHeat_sections_movingValues d aux z z₀ p p₀ K K₀ ω hz hc hK).2.2.1
  have hJ := hp.mono fun ω hc=>(pathHeat_sections_movingValues d aux z z₀ p p₀ K K₀ ω hz hc hK).2.2.2
  have ht := pathHeat_normalized_limits hn h hW hF hH hJ
  have hIH := pathHeat_tendsto_weighted_integral h.integrable_envelope h.nonneg_C
    (fun i=>(hn i).weight_measurable) (fun i=>(hn i).density_generator_measurable)
    (fun i=>(hn i).weight_positive) (fun i=>(hn i).weight_bound)
    (fun i=>(hn i).density_generator_bound) hW hH
  exact ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,hIH.div ht.2.1 ht.1.ne'⟩

end HexagonPaper
