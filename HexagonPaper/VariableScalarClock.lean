module
public import HexagonPaper.PrefixLikelihoodPrinted
public import Mathlib.Topology.Order.MonotoneContinuity

@[expose] public section

/-! Exact scalar prefix likelihood under an arbitrary increasing continuous
clock. This is a genuine time-change bridge for arbitrary atomic profiles,
not a claim that an analytic mixture clock exhausts all bounded coefficient
functions. Identification of a primitive coefficient clock and of its
original deterministic Itô driver is a separate obligation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open QuantitativeFollowup QuantitativePaper
open scoped NNReal ENNReal Topology
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def scalarClockMeasure (τ : Paper.Overlap≃oPaper.Overlap) (μ : Paper.ParisiMeasure) :
    Paper.ParisiMeasure := μ.map τ

theorem scalarClockMeasure_cdf (τ : Paper.Overlap≃oPaper.Overlap)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Paper.parisiCDF (scalarClockMeasure τ μ) (τ q)=Paper.parisiCDF μ q := by
  have hm : MeasurableSet {r : Paper.Overlap | (r:ℝ)≤(τ q:ℝ)} :=
    (isClosed_le continuous_subtype_val continuous_const).measurableSet
  unfold Paper.parisiCDF scalarClockMeasure
  rw [ProbabilityMeasure.map_apply' μ τ.continuous.measurable.aemeasurable hm]
  congr 1
  congr 1
  ext r
  exact τ.le_iff_le

def scalarClockPathReindex (τ : Paper.Overlap≃oPaper.Overlap) (Z : C(Paper.Overlap,ℝ)) :
    C(Paper.Overlap,ℝ) := Z.comp ⟨τ,τ.continuous⟩

theorem measurable_scalarClockPathReindex (τ : Paper.Overlap≃oPaper.Overlap) :
    Measurable (scalarClockPathReindex τ) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro q
  exact ContinuousMap.measurable_eval (τ q)

def scalarClockPotential (τ : Paper.Overlap≃oPaper.Overlap) (β : ℝ)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (x : ℝ) : ℝ :=
  scalarPrintedPotential β (scalarClockMeasure τ μ) (τ q) x

def scalarClockReference (τ : Paper.Overlap≃oPaper.Overlap) (β : ℝ)
    (sample : Paper.BrownianSample) (q : Paper.Overlap) : ℝ :=
  β*canonicalBrownian (τ q:ℝ).toNNReal sample

def scalarClockPrefixDensity (τ : Paper.Overlap≃oPaper.Overlap) (β : ℝ)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : Paper.BrownianSample) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (Paper.parisiCDF μ q*
    scalarClockPotential τ β μ q (scalarClockReference τ β sample q)-
      ∫r : Paper.Overlap,if r≤q then scalarClockPotential τ β μ r
        (scalarClockReference τ β sample r) else 0 ∂(μ:Measure Paper.Overlap)))

def scalarClockStoppedReferencePath (τ : Paper.Overlap≃oPaper.Overlap) (β : ℝ)
    (q : Paper.Overlap) (sample : Paper.BrownianSample) : C(Paper.Overlap,ℝ) :=
  scalarClockPathReindex τ (scalarStoppedBrownianPath β (τ q:ℝ).toNNReal sample)

def scalarClockStoppedStatePath (τ : Paper.Overlap≃oPaper.Overlap) (β : ℝ)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : Paper.BrownianSample) :
    C(Paper.Overlap,ℝ) :=
  scalarClockPathReindex τ (scalarStoppedStatePath β (scalarClockMeasure τ μ) (τ q:ℝ).toNNReal sample)

theorem scalarClockPrefixDensity_eq_native (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : Paper.BrownianSample) :
    scalarClockPrefixDensity τ β μ q sample=
      scalarPrintedPrefixDensity β (scalarClockMeasure τ μ) (τ q:ℝ).toNNReal sample := by
  let ν:=scalarClockMeasure τ μ
  let F:Paper.Overlap→ℝ:=fun r=>scalarPrintedPotential β ν r
    (β*canonicalBrownian (r:ℝ).toNNReal sample)
  have hF : Continuous F:=by
    unfold F scalarPrintedPotential
    exact continuous_const.add ((continuous_parisiPotential β ν).comp
      (continuous_subtype_val.prodMk (((continuous_canonicalBrownian sample).comp
        (continuous_real_toNNReal.comp continuous_subtype_val)).const_mul β)))
  have hi : (∫r : Paper.Overlap,if r≤τ q then F r else 0 ∂(ν:Measure Paper.Overlap))=
      ∫r : Paper.Overlap,if r≤q then F (τ r) else 0 ∂(μ:Measure Paper.Overlap) := by
    have hm : Measurable (fun r : Paper.Overlap=>if r≤τ q then F r else 0) :=
      hF.measurable.ite (isClosed_le continuous_id continuous_const).measurableSet measurable_const
    change (∫r : Paper.Overlap,if r≤τ q then F r else 0
      ∂(μ:Measure Paper.Overlap).map τ)=_
    rw [integral_map τ.continuous.measurable.aemeasurable hm.aestronglyMeasurable]
    congr 1
    funext r
    simp only [τ.le_iff_le]
  unfold scalarClockPrefixDensity scalarPrintedPrefixDensity scalarClockPotential scalarClockReference
  simp only [Real.coe_toNNReal _ (τ q).property.1]
  rw [scalarClockMeasure_cdf]
  congr 2
  congr 1
  exact hi.symm

theorem scalarClockStoppedPath_likelihood (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    canonicalBrownianMeasure.map (scalarClockStoppedStatePath τ β μ q)=
      (canonicalBrownianMeasure.withDensity (scalarClockPrefixDensity τ β μ q)).map
        (scalarClockStoppedReferencePath τ β q) := by
  have ht : ((τ q:ℝ).toNNReal:ℝ)≤1 := by
    rw [Real.coe_toNNReal _ (τ q).property.1]
    exact (τ q).property.2
  have he:=congrArg (fun P : Measure C(Paper.Overlap,ℝ)=>P.map (scalarClockPathReindex τ))
    (scalarStoppedPath_printed_likelihood β hβ (scalarClockMeasure τ μ) (τ q:ℝ).toNNReal ht)
  rw [Measure.map_map (measurable_scalarClockPathReindex τ)
    (measurable_scalarStoppedStatePath β hβ (scalarClockMeasure τ μ) _ ht),
    Measure.map_map (measurable_scalarClockPathReindex τ) (measurable_scalarStoppedBrownianPath β _)] at he
  have hw : scalarClockPrefixDensity τ β μ q=
      scalarPrintedPrefixDensity β (scalarClockMeasure τ μ) (τ q:ℝ).toNNReal :=
    funext (scalarClockPrefixDensity_eq_native τ β μ q)
  rw [←hw] at he
  exact he

end HexagonPaper
