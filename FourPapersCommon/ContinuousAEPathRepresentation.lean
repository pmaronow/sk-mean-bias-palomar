module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.DenseEmbedding
public import FourPapersCommon.BrownianClockRescaling
public import Mathlib.Probability.Process.FiniteDimensionalLaws

@[expose] public section

/-! An almost-everywhere continuous process has a genuine measurable
continuous-path representative. Countably many dense evaluations share
one null set; no uncountable product measurability is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace FourPapersCommon

theorem exists_measurable_continuous_path_representative
    {Ω K : Type*} [MeasurableSpace Ω] [MetricSpace K]
    [CompactSpace K] [SecondCountableTopology K]
    (P : Measure Ω) (X : K→Ω→ℝ)
    (hX : ∀t,AEMeasurable (X t) P)
    (hc : ∀ᵐω∂P,Continuous (fun t=>X t ω)) :
    ∃Y : Ω→C(K,ℝ),Measurable Y ∧
      ∀ᵐω∂P,∀t,Y ω t=X t ω := by
  classical
  let φ : Ω→C(K,ℝ) := fun ω=>if h : Continuous (fun t=>X t ω)
    then ⟨fun t=>X t ω,h⟩ else 0
  have heval (t : K) : AEMeasurable (fun ω=>φ ω t) P := by
    apply (hX t).congr
    filter_upwards [hc] with ω hω
    simp only [φ,dite_eq_left hω,ContinuousMap.coe_mk]
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense K
  letI : Countable D := hDc.to_subtype
  let e : C(K,ℝ)→(D→ℝ) := fun f t=>f t
  have he : Continuous e := continuous_pi fun t=>continuous_eval_const t.1
  have hi : Function.Injective e := by
    intro f g hfg
    apply ContinuousMap.coe_injective
    exact hDd.denseRange_val.equalizer f.continuous g.continuous hfg
  have hEmb : MeasurableEmbedding e := he.measurableEmbedding hi
  have hφ : AEMeasurable φ P := hEmb.aemeasurable_comp_iff.mp
    (AEMeasurable.of_eval fun t=>heval t.1)
  refine ⟨hφ.mk φ,hφ.measurable_mk,?_⟩
  filter_upwards [hφ.ae_eq_mk,hc] with ω hω hcont
  intro t
  rw [←hω]
  simp only [φ,dite_eq_left hcont,ContinuousMap.coe_mk]

theorem continuous_path_law_eq_of_finite_evaluations
    {Ω K : Type*} [MeasurableSpace Ω] [MetricSpace K]
    [CompactSpace K] [SecondCountableTopology K]
    (P : Measure Ω) [IsFiniteMeasure P]
    (X Y : Ω→C(K,ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hfinite : ∀I : Finset K,
      P.map (fun ω=>I.restrict (fun t=>X ω t))=
        P.map (fun ω=>I.restrict (fun t=>Y ω t))) :
    P.map X=P.map Y := by
  apply continuousRealPathMeasure_ext
  rw [Measure.map_map measurable_continuousRealPath_coe hX,
    Measure.map_map measurable_continuousRealPath_coe hY]
  exact (ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq
    (measurable_continuousRealPath_coe.comp hX).aemeasurable
    (measurable_continuousRealPath_coe.comp hY).aemeasurable).mpr hfinite

end FourPapersCommon
