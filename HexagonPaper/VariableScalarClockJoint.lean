module
public import HexagonPaper.VariableScalarClock
public import HexagonPaper.PrefixLikelihoodJoint

@[expose] public section

/-! Atom-preserving marked-joint scalar likelihood under an arbitrary
increasing clock. No covariance-mixture restriction enters the transport. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open QuantitativeFollowup QuantitativePaper
open scoped NNReal ENNReal Topology
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem scalarClock_zero (τ : Paper.Overlap≃oPaper.Overlap) : τ zeroOverlap=zeroOverlap :=
  τ.map_bot

theorem scalarClock_one (τ : Paper.Overlap≃oPaper.Overlap) : τ (1:Paper.Overlap)=1 :=
  τ.map_top

theorem scalarClockMeasure_floor (τ : Paper.Overlap≃oPaper.Overlap)
    (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ∈scalarFloor a) :
    scalarClockMeasure τ μ∈scalarFloor a := by
  rw [mem_scalarFloor_iff,zeroMass_eq_parisiCDF_zero] at hμ ⊢
  have he:=scalarClockMeasure_cdf τ μ zeroOverlap
  rw [scalarClock_zero] at he
  exact he.symm ▸ hμ

def scalarClockJointDensity (τ : Paper.Overlap≃oPaper.Overlap) (β : ℝ)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.BrownianSample×Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (Paper.spinSign p.2*scalarClockReference τ β p.1 1-
    a*scalarClockPotential τ β μ zeroOverlap 0-
      ∫r,scalarClockPotential τ β μ r (scalarClockReference τ β p.1 r)
        ∂parisiFreeMeasure μ a))

theorem scalarClockJointDensity_eq_native (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) (p : Paper.BrownianSample×Bool) :
    scalarClockJointDensity τ β μ a p=
      scalarPrintedBrownianFreeDensity β (scalarClockMeasure τ μ) a p := by
  let ν:=scalarClockMeasure τ μ
  let F:Paper.Overlap→ℝ:=fun r=>scalarPrintedPotential β ν r
    (β*canonicalBrownian (r:ℝ).toNNReal p.1)
  have hF : Continuous F:=by
    unfold F scalarPrintedPotential
    exact continuous_const.add ((continuous_parisiPotential β ν).comp
      (continuous_subtype_val.prodMk (((continuous_canonicalBrownian p.1).comp
        (continuous_real_toNNReal.comp continuous_subtype_val)).const_mul β)))
  have hi : (∫r,F r ∂parisiFreeMeasure ν a)=
      ∫r,F (τ r) ∂parisiFreeMeasure μ a := by
    rw [integral_parisiFreeMeasure_continuous ν a ha (scalarClockMeasure_floor τ μ a hμ) F hF,
      integral_parisiFreeMeasure_continuous μ a ha hμ (fun r=>F (τ r))
        (show Continuous (fun r=>F (τ r)) from hF.comp τ.continuous)]
    change (∫r,F r ∂(μ:Measure Paper.Overlap).map τ)-a*F zeroOverlap=_
    rw [integral_map τ.continuous.measurable.aemeasurable hF.measurable.aestronglyMeasurable,
      scalarClock_zero]
  unfold scalarClockJointDensity scalarPrintedBrownianFreeDensity scalarClockPotential scalarClockReference
  rw [scalarClock_one,scalarClock_zero]
  simp only [show ((1:Paper.Overlap):ℝ).toNNReal=1 by norm_num,
    show (zeroOverlap:ℝ)=0 from rfl]
  change ENNReal.ofReal (Real.exp (Paper.spinSign p.2*(β*canonicalBrownian 1 p.1)-
      a*scalarPrintedPotential β ν 0 0-∫r,F (τ r) ∂parisiFreeMeasure μ a))=
    ENNReal.ofReal (Real.exp (Paper.spinSign p.2*(β*canonicalBrownian 1 p.1)-
      a*scalarPrintedPotential β ν 0 0-∫r,F r ∂parisiFreeMeasure ν a))
  rw [hi]

theorem scalarClockMarkedSpinLaw_likelihood (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) :
    (scalarMarkedSpinLaw β hβ (scalarClockMeasure τ μ)).map
      (fun p=>(scalarClockStoppedStatePath τ β μ 1 p.1,p.2))=
      ((canonicalBrownianMeasure.prod (Measure.count:Measure Bool)).withDensity
        (scalarClockJointDensity τ β μ a)).map
          (fun p=>(scalarClockStoppedReferencePath τ β 1 p.1,p.2)) := by
  let R:C(Paper.Overlap,ℝ)×Bool→C(Paper.Overlap,ℝ)×Bool:=
    fun p=>(scalarClockPathReindex τ p.1,p.2)
  have hR : Measurable R:=((measurable_scalarClockPathReindex τ).comp measurable_fst).prodMk measurable_snd
  have he:=congrArg (fun Q:Measure (C(Paper.Overlap,ℝ)×Bool)=>Q.map R)
    (scalarMarkedSpinLaw_fullPath_printed_density β hβ (scalarClockMeasure τ μ) a ha
      (scalarClockMeasure_floor τ μ a hμ))
  have hmV : Measurable (fun p : Paper.BrownianSample×Bool=>
      (scalarStoppedStatePath β (scalarClockMeasure τ μ) 1 p.1,p.2)) :=
    ((measurable_scalarStoppedStatePath β hβ (scalarClockMeasure τ μ)
      1 (by norm_num)).comp measurable_fst).prodMk measurable_snd
  have hmY : Measurable (fun p : Paper.BrownianSample×Bool=>
      (scalarStoppedBrownianPath β 1 p.1,p.2)) :=
    ((measurable_scalarStoppedBrownianPath β 1).comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_map hR hmV,Measure.map_map hR hmY] at he
  have hw : scalarClockJointDensity τ β μ a=scalarPrintedBrownianFreeDensity β (scalarClockMeasure τ μ) a :=
    funext (scalarClockJointDensity_eq_native τ β μ a ha hμ)
  rw [←hw] at he
  unfold scalarClockStoppedStatePath scalarClockStoppedReferencePath
  rw [scalarClock_one,show ((1:Paper.Overlap):ℝ).toNNReal=1 by norm_num]
  exact he

end HexagonPaper
