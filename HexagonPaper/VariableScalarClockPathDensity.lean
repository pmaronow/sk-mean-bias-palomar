module
public import HexagonPaper.VariableScalarClockJoint
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Exact likelihoods on continuous path space under an arbitrary clock.
These densities depend on the actual path, allowing replacement of the
time-changed reference by its genuine deterministic Itô realization. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB FourPapersCommon QuantitativeFollowup QuantitativePaper
open scoped Topology ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

def scalarClockPrefixPathDensity (τ : Paper.Overlap≃oPaper.Overlap) (β : ℝ)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (Z : C(Paper.Overlap,ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (parisiCDF μ q*scalarClockPotential τ β μ q (Z q)-
    ∫r : Paper.Overlap,if r≤q then scalarClockPotential τ β μ r (Z r) else 0
      ∂(μ:Measure Paper.Overlap)))

theorem continuous_scalarClockPotential (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (μ : Paper.ParisiMeasure) :
    Continuous (fun p : Paper.Overlap×ℝ=>scalarClockPotential τ β μ p.1 p.2) :=
  continuous_const.add ((continuous_parisiPotential β (scalarClockMeasure τ μ)).comp
    ((continuous_subtype_val.comp (τ.continuous.comp continuous_fst)).prodMk continuous_snd))

set_option backward.isDefEq.respectTransparency true in
theorem measurable_scalarClockPrefixPathDensity (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Measurable (scalarClockPrefixPathDensity τ β μ q) := by
  unfold scalarClockPrefixPathDensity
  have hev : Continuous (fun p : C(Paper.Overlap,ℝ)×Paper.Overlap=>p.1 p.2):=continuous_eval
  let A:C(Paper.Overlap×ℝ,ℝ):=⟨fun p=>scalarClockPotential τ β μ p.1 p.2,
    continuous_scalarClockPotential τ β μ⟩
  let P:C(C(Paper.Overlap,ℝ)×Paper.Overlap,Paper.Overlap×ℝ):=
    ⟨fun p=>(p.2,p.1 p.2),continuous_snd.prodMk hev⟩
  have hF : Continuous (fun p : C(Paper.Overlap,ℝ)×Paper.Overlap=>
      scalarClockPotential τ β μ p.2 (p.1 p.2)) := by
    convert (A.comp P).continuous using 1
    rfl
  have hrestriction (Z : C(Paper.Overlap,ℝ)) :
      (∫r : Paper.Overlap,if r≤q then scalarClockPotential τ β μ r (Z r) else 0
        ∂(μ:Measure Paper.Overlap))=
      ∫r in Iic q,scalarClockPotential τ β μ r (Z r) ∂(μ:Measure Paper.Overlap) := by
    rw [←integral_indicator measurableSet_Iic]
    rfl
  have hi : Measurable (fun Z : C(Paper.Overlap,ℝ)=>
      ∫r in Iic q,scalarClockPotential τ β μ r (Z r) ∂(μ:Measure Paper.Overlap)) :=
    hF.measurable.stronglyMeasurable.integral_prod_right'.measurable
  have hpair : Measurable (fun Z:C(Paper.Overlap,ℝ)=>(q,Z q)) :=
    measurable_const.prodMk (ContinuousMap.measurable_eval q)
  have he : Measurable (fun Z : C(Paper.Overlap,ℝ)=>scalarClockPotential τ β μ q (Z q)) := by
    convert A.continuous.measurable.comp hpair using 1
    rfl
  simp_rw [hrestriction]
  exact ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.measurable.comp ((measurable_const.mul he).sub hi))


theorem scalarClockStoppedReferencePath_apply (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (q r : Paper.Overlap) (sample : Paper.BrownianSample) :
    scalarClockStoppedReferencePath τ β q sample r=
      scalarClockReference τ β sample (min r q) := by
  change β*canonicalBrownian (stoppedOverlapTime (τ q:ℝ).toNNReal (τ r)) sample=_
  congr 1
  congr 1
  apply NNReal.eq
  simp only [stoppedOverlapTime,NNReal.coe_mk,Real.coe_toNNReal _ (τ q).property.1,
    Real.coe_toNNReal _ (τ (min r q)).property.1]
  change min (τ r:ℝ) (τ q:ℝ)=(τ (min r q):ℝ)
  exact congrArg Subtype.val ((τ.monotone.map_min (a:=r) (b:=q)).symm)


theorem scalarClockPrefixPathDensity_reference (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : Paper.BrownianSample) :
    scalarClockPrefixPathDensity τ β μ q (scalarClockStoppedReferencePath τ β q sample)=
      scalarClockPrefixDensity τ β μ q sample := by
  unfold scalarClockPrefixPathDensity scalarClockPrefixDensity
  rw [scalarClockStoppedReferencePath_apply, min_self]
  congr 2
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr:r≤q
  · rw [if_pos hr,if_pos hr,scalarClockStoppedReferencePath_apply,min_eq_left hr]
  · rw [if_neg hr,if_neg hr]


theorem measurable_scalarClockStoppedReferencePath (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (q : Paper.Overlap) : Measurable (scalarClockStoppedReferencePath τ β q) :=
  (measurable_scalarClockPathReindex τ).comp (measurable_scalarStoppedBrownianPath β _)


theorem scalarClockStoppedPath_likelihood_path (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    canonicalBrownianMeasure.map (scalarClockStoppedStatePath τ β μ q)=
      (canonicalBrownianMeasure.map (scalarClockStoppedReferencePath τ β q)).withDensity
        (scalarClockPrefixPathDensity τ β μ q) := by
  rw [←FRSB.map_withDensity_pullback _ _ (measurable_scalarClockStoppedReferencePath τ β q)
    _ (measurable_scalarClockPrefixPathDensity τ β μ q)]
  change canonicalBrownianMeasure.map (scalarClockStoppedStatePath τ β μ q)=
    (canonicalBrownianMeasure.withDensity
      (fun sample=>scalarClockPrefixPathDensity τ β μ q
        (scalarClockStoppedReferencePath τ β q sample))).map _
  simp only [scalarClockPrefixPathDensity_reference]
  exact scalarClockStoppedPath_likelihood τ β hβ μ q


def scalarClockJointPathDensity (τ : Paper.Overlap≃oPaper.Overlap) (β : ℝ)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : C(Paper.Overlap,ℝ)×Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (spinSign p.2*p.1 1-
    a*scalarClockPotential τ β μ zeroOverlap 0-
    ∫r,scalarClockPotential τ β μ r (p.1 r) ∂parisiFreeMeasure μ a))

set_option backward.isDefEq.respectTransparency true in
theorem measurable_scalarClockJointPathDensity (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) :
    Measurable (scalarClockJointPathDensity τ β μ a) := by
  unfold scalarClockJointPathDensity
  have hev : Continuous (fun p : C(Paper.Overlap,ℝ)×Paper.Overlap=>p.1 p.2):=continuous_eval
  let A:C(Paper.Overlap×ℝ,ℝ):=⟨fun p=>scalarClockPotential τ β μ p.1 p.2,
    continuous_scalarClockPotential τ β μ⟩
  let P:C(C(Paper.Overlap,ℝ)×Paper.Overlap,Paper.Overlap×ℝ):=
    ⟨fun p=>(p.2,p.1 p.2),continuous_snd.prodMk hev⟩
  have hF : Continuous (fun p : C(Paper.Overlap,ℝ)×Paper.Overlap=>
      scalarClockPotential τ β μ p.2 (p.1 p.2)) := by
    convert (A.comp P).continuous using 1
    rfl
  have hi : Measurable (fun Z : C(Paper.Overlap,ℝ)=>
      ∫r,scalarClockPotential τ β μ r (Z r) ∂parisiFreeMeasure μ a) :=
    hF.measurable.stronglyMeasurable.integral_prod_right'.measurable
  have hs:Measurable (fun p : C(Paper.Overlap,ℝ)×Bool=>spinSign p.2):=
    (measurable_of_finite spinSign).comp measurable_snd
  exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
    (((hs.mul ((ContinuousMap.measurable_eval 1).comp measurable_fst)).sub measurable_const).sub
      (hi.comp measurable_fst)))


theorem scalarClockJointPathDensity_reference (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (sample : Paper.BrownianSample×Bool) :
    scalarClockJointPathDensity τ β μ a
      (scalarClockStoppedReferencePath τ β 1 sample.1,sample.2)=
        scalarClockJointDensity τ β μ a sample := by
  unfold scalarClockJointPathDensity scalarClockJointDensity
  have hmin (r : Paper.Overlap) : min r 1=r:=min_eq_left r.property.2
  simp only [scalarClockStoppedReferencePath_apply,hmin]

theorem scalarClockMarkedSpinLaw_likelihood_path (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) :
    (scalarMarkedSpinLaw β hβ (scalarClockMeasure τ μ)).map
      (fun p=>(scalarClockStoppedStatePath τ β μ 1 p.1,p.2))=
      ((canonicalBrownianMeasure.prod (Measure.count:Measure Bool)).map
        (fun p=>(scalarClockStoppedReferencePath τ β 1 p.1,p.2))).withDensity
          (scalarClockJointPathDensity τ β μ a) := by
  have hm : Measurable (fun p : Paper.BrownianSample×Bool=>
      (scalarClockStoppedReferencePath τ β 1 p.1,p.2)):=
    ((measurable_scalarClockStoppedReferencePath τ β 1).comp measurable_fst).prodMk measurable_snd
  rw [←FRSB.map_withDensity_pullback _ _ hm _
    (measurable_scalarClockJointPathDensity τ β μ a)]
  change _=((canonicalBrownianMeasure.prod (Measure.count:Measure Bool)).withDensity
    (fun p=>scalarClockJointPathDensity τ β μ a
      (scalarClockStoppedReferencePath τ β 1 p.1,p.2))).map _
  simp only [scalarClockJointPathDensity_reference]
  exact scalarClockMarkedSpinLaw_likelihood τ β hβ μ a ha hμ

end HexagonPaper
