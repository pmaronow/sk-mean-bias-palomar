module
public import QuantitativeFollowup.ScalarTransport

@[expose] public section

/-! Weak continuity of the actual transported overlap law and preservation
of its exact root mass under a sufficiently small increasing transport. -/
noncomputable section
open Set Filter MeasureTheory Paper FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem continuous_scalarLevelTransport_parameter (φ : C(Paper.Overlap,ℝ)) (θ : ℝ) :
    Continuous (scalarLevelTransport φ θ) := by
  convert! (continuous_scalarLevelTransport φ).comp (continuous_const.prodMk continuous_id) using 1

 theorem continuous_scalarTransportMeasure (φ : C(Paper.Overlap,ℝ)) :
    Continuous (fun z : Paper.ParisiMeasure×ℝ => scalarTransportMeasure z.1 φ z.2) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  have hf : Continuous (fun z : (Paper.ParisiMeasure×ℝ)×Paper.Overlap =>
      f (scalarLevelTransport φ z.1.2 z.2)) :=
    f.continuous.comp ((continuous_scalarLevelTransport φ).comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  have hi := continuous_integral_probability_family
    (fun z : (Paper.ParisiMeasure×ℝ)×Paper.Overlap => f (scalarLevelTransport φ z.1.2 z.2)) hf
    (fun z : Paper.ParisiMeasure×ℝ => z.1) continuous_fst
  convert! hi using 1
  funext z
  rw [scalarTransportMeasure,ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_scalarLevelTransport_parameter φ z.2).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]

 theorem scalarLevelTransport_root (φ : C(Paper.Overlap,ℝ)) (h0 : φ 0=0) (θ : ℝ) :
    scalarLevelTransport φ θ 0=0 := by
  apply Subtype.ext
  simp only [scalarLevelTransport,h0,mul_zero,add_zero]
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one (by constructor <;> norm_num))

 theorem scalarLevelTransport_root_preimage (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (θ : ℝ)
    (hθ : |θ| *L < 1) : scalarLevelTransport φ θ ⁻¹' {(0 : Paper.Overlap)}={(0 : Paper.Overlap)} := by
  ext q
  simp only [mem_preimage,mem_singleton_iff]
  constructor
  · intro h
    apply (strictMono_scalarLevelTransport φ L hφ h0 h1 θ hθ).injective
    rw [h,scalarLevelTransport_root φ h0 θ]
  · intro h
    rw [h,scalarLevelTransport_root φ h0 θ]

 theorem scalarTransportMeasure_root_mass (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (θ : ℝ)
    (hθ : |θ| *L < 1) :
    (scalarTransportMeasure μ φ θ : Measure Paper.Overlap) {(0 : Paper.Overlap)}=
      (μ : Measure Paper.Overlap) {(0 : Paper.Overlap)} := by
  rw [scalarTransportMeasure,ProbabilityMeasure.map_apply' μ
    ((continuous_scalarLevelTransport_parameter φ θ).measurable.aemeasurable)
    (measurableSet_singleton _),scalarLevelTransport_root_preimage φ L hφ h0 h1 θ hθ]

 theorem scalarTransportMeasure_mem_scalarFloor (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ))
    (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (θ : ℝ)
    (hθ : |θ| *L < 1) (s : ℝ) (hμ : μ∈scalarFloor s) :
    scalarTransportMeasure μ φ θ∈scalarFloor s := by
  change ENNReal.ofReal s ≤ (scalarTransportMeasure μ φ θ : Measure Paper.Overlap) {zeroOverlap}
  change ENNReal.ofReal s ≤ (μ : Measure Paper.Overlap) {zeroOverlap} at hμ
  change ENNReal.ofReal s ≤ (scalarTransportMeasure μ φ θ : Measure Paper.Overlap) {(0 : Paper.Overlap)}
  rw [scalarTransportMeasure_root_mass μ φ L hφ h0 h1 θ hθ]
  exact hμ

end QuantitativeFollowup
