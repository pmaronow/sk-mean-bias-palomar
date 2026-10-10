module
public import QuantitativePaper.VectorOffDiagonalMoment
public import QuantitativePaper.VectorMeasureDisorderTilt
public import FourPapersCommon.IndependentProductTilt

@[expose] public section

/-! The actual disorder tilt factorizes into its off-diagonal SK tilt and
independent common-diagonal tilt. The off-diagonal marginal is unchanged
by adding the common completion Gaussian. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace QuantitativePaper
open FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def vectorOffDiagonalOuterLaw (μ : Paper.ParisiMeasure) (β t a : ℝ) :
    Measure (Couplings n) :=
  (couplingLaw n).tilted (fun g => a * vectorMeasurePotential μ β t (g,0) 0)

theorem vectorOffDiagonalOuterLaw_probability (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) :
    IsProbabilityMeasure (vectorOffDiagonalOuterLaw (n:=n) μ β t a) :=
  isProbabilityMeasure_tilted (integrable_exp_vectorMeasurePotential_offDiagonal μ β t ht a 0)

theorem vectorMeasureOuterLaw_diagonal_product (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) :
    vectorMeasureOuterLaw (n:=n) μ β t a =
      (vectorOffDiagonalOuterLaw μ β t a).prod
        ((gaussianReal 0 (1/2)).tilted (fun z : ℝ => (a*β*Real.sqrt t)*z)) := by
  let insert : Couplings n → Couplings n × ℝ := fun g => (g,0)
  have hi : Measurable insert := measurable_id.prodMk measurable_const
  have hf : Measurable (fun g : Couplings n => a * vectorMeasurePotential μ β t (g,0) 0) := by
    convert! (measurable_const (a:=a)).mul
      ((measurable_vectorMeasurePotential_initial (n:=n) μ β t ht).comp hi) using 1
  have he : (fun p : Couplings n × ℝ => a * vectorMeasurePotential μ β t p 0) =
      fun p => a * vectorMeasurePotential μ β t (p.1,0) 0 + (a*β*Real.sqrt t)*p.2 := by
    funext p
    rw [vectorMeasurePotential_diagonal_shift μ β t ht p 0]
    ring
  change (completionLaw n).tilted (fun p => a * vectorMeasurePotential μ β t p 0) = _
  rw [completionLaw, he]
  exact tilted_prod_add (couplingLaw n) (gaussianReal 0 (1/2))
    (fun g : Couplings n => a * vectorMeasurePotential μ β t (g,0) 0)
    (fun z : ℝ => (a*β*Real.sqrt t)*z) hf
    ((measurable_const (a:=a*β*Real.sqrt t)).mul measurable_id)
    (integrable_exp_vectorMeasurePotential_offDiagonal μ β t ht a 0)
    (integrable_exp_mul_gaussianReal (μ:=0) (v:=1/2) (a*β*Real.sqrt t))

theorem vectorMeasureOuterLaw_offDiagonal_marginal (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) :
    (vectorMeasureOuterLaw (n:=n) μ β t a).map Prod.fst =
      vectorOffDiagonalOuterLaw μ β t a := by
  haveI := vectorOffDiagonalOuterLaw_probability (n:=n) μ β t a ht
  haveI := isProbabilityMeasure_tilted
    (integrable_exp_mul_gaussianReal (μ:=0) (v:=1/2) (a*β*Real.sqrt t))
  rw [vectorMeasureOuterLaw_diagonal_product μ β t a ht]
  exact measurePreserving_fst.map_eq

end QuantitativePaper
