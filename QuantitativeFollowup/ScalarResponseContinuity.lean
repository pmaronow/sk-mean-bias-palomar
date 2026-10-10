module
public import QuantitativeFollowup.ScalarResponseRegrouping

@[expose] public section

/-! Literal continuity and weak approximation of the seven-term scalar J.
The proof uses its exact regrouping, so strict-future intervals and atoms
are retained. This does not identify J with a transport derivative. -/
noncomputable section
open Set Filter MeasureTheory Paper FourPapersCommon QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

 theorem continuous_scalarResponseOperator_floor (β : ℝ) (hβ : β ≠ 0)
    (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) (φ : C(Paper.Overlap,ℝ)) :
    Continuous (fun z : ScalarFloorMeasure s×Paper.Overlap => scalarResponseOperator β hβ z.1.val s φ z.2) := by
  have he : (fun z : ScalarFloorMeasure s×Paper.Overlap => scalarResponseOperator β hβ z.1.val s φ z.2)=
      (fun z => scalarRegroupedResponse β z.1.val s φ z.2) := by
    funext z
    exact scalarResponseOperator_eq_regrouped β hβ z.1.val s hs z.1.property φ z.2
  rw [he]
  exact continuous_scalarRegroupedResponse β hβ s hs φ

 theorem continuous_scalarResponseOperator (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor s) (φ : C(Paper.Overlap,ℝ)) :
    Continuous (scalarResponseOperator β hβ μ s φ) := by
  have harg : Continuous (fun p : Paper.Overlap => ((⟨μ,hμ⟩ : ScalarFloorMeasure s),p)) :=
    continuous_const.prodMk continuous_id
  convert! (continuous_scalarResponseOperator_floor β hβ s hs φ).comp harg using 1

 def scalarResponseContinuousMap (β : ℝ) (hβ : β ≠ 0) (s : ℝ)
    (hs : s∈Icc (0 : ℝ) 1) (φ : C(Paper.Overlap,ℝ)) (μ : ScalarFloorMeasure s) : C(Paper.Overlap,ℝ) :=
  ⟨scalarResponseOperator β hβ μ.val s φ,continuous_scalarResponseOperator β hβ μ.val s hs μ.property φ⟩

 theorem continuous_scalarResponseContinuousMap (β : ℝ) (hβ : β ≠ 0) (s : ℝ)
    (hs : s∈Icc (0 : ℝ) 1) (φ : C(Paper.Overlap,ℝ)) :
    Continuous (scalarResponseContinuousMap β hβ s hs φ) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_scalarResponseOperator_floor β hβ s hs φ)

 theorem tendstoUniformly_scalarResponseOperator_of_weak {ι : Type*} {L : Filter ι}
    (β : ℝ) (hβ : β ≠ 0) (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) (φ : C(Paper.Overlap,ℝ))
    (μs : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure)
    (hfloor : ∀ i,μs i∈scalarFloor s) (hμ : μ∈scalarFloor s)
    (hweak : Tendsto μs L (𝓝 μ)) :
    TendstoUniformly (fun i => scalarResponseOperator β hβ (μs i) s φ)
      (scalarResponseOperator β hβ μ s φ) L := by
  let μs' : ι → ScalarFloorMeasure s := fun i => ⟨μs i,hfloor i⟩
  let μ' : ScalarFloorMeasure s := ⟨μ,hμ⟩
  have h : Tendsto μs' L (𝓝 μ') := tendsto_subtype_rng.mpr hweak
  have hC := (continuous_scalarResponseContinuousMap β hβ s hs φ).continuousAt.tendsto.comp h
  exact ContinuousMap.tendsto_iff_tendstoUniformly.mp hC

 theorem tendsto_probability_of_free_integrals {ι : Type*} {L : Filter ι}
    (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) (μs : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure)
    (hfloor : ∀ i,μs i∈scalarFloor s) (hμ : μ∈scalarFloor s)
    (hweak : ∀ f : C(Paper.Overlap,ℝ),
      Tendsto (fun i => ∫ q,f q ∂parisiFreeMeasure (μs i) s) L
        (𝓝 (∫ q,f q ∂parisiFreeMeasure μ s))) : Tendsto μs L (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let g : C(Paper.Overlap,ℝ) := ⟨f,f.continuous⟩
  have he (ν : Paper.ParisiMeasure) (hf : ν∈scalarFloor s) :
      (∫ q,f q ∂(ν : Measure Paper.Overlap))=(∫ q,f q ∂parisiFreeMeasure ν s)+s*f zeroOverlap := by
    have hi := integral_parisiFreeMeasure_continuous ν s hs hf f f.continuous
    linarith
  simp_rw [he _ (hfloor _),he _ hμ]
  convert! (hweak g).add_const (s*f zeroOverlap) using 1

 theorem tendstoUniformly_scalarResponseOperator_of_free_weak {ι : Type*} {L : Filter ι}
    (β : ℝ) (hβ : β ≠ 0) (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) (φ : C(Paper.Overlap,ℝ))
    (μs : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure)
    (hfloor : ∀ i,μs i∈scalarFloor s) (hμ : μ∈scalarFloor s)
    (hweak : ∀ f : C(Paper.Overlap,ℝ),
      Tendsto (fun i => ∫ q,f q ∂parisiFreeMeasure (μs i) s) L
        (𝓝 (∫ q,f q ∂parisiFreeMeasure μ s))) :
    TendstoUniformly (fun i => scalarResponseOperator β hβ (μs i) s φ)
      (scalarResponseOperator β hβ μ s φ) L :=
  tendstoUniformly_scalarResponseOperator_of_weak β hβ s hs φ μs μ hfloor hμ
    (tendsto_probability_of_free_integrals s hs μs μ hfloor hμ hweak)

end QuantitativeFollowup
