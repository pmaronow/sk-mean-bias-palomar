module
public import QuantitativePaper.VectorDiagonalDynamics
public import QuantitativePaper.VectorDiagonalTilt
public import QuantitativePaper.VectorTiltedBrownian
public import QuantitativePaper.VectorDyadicSpinMeanConvergence

@[expose] public section

/-! Exact law of the actual diffusion sample with the common diagonal
completion removed, and invariance of its physical spin means. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def vectorOffDiagonalCompletion (g : Couplings n) : Couplings n×ℝ := (g,0)

theorem measurable_vectorOffDiagonalCompletion : Measurable (vectorOffDiagonalCompletion (n:=n)) :=
  measurable_id.prodMk measurable_const

theorem vectorMeasureOuterLaw_removeDiagonal (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) :
    (vectorMeasureOuterLaw (n:=n) μ β t a).map (fun p => (p.1,(0:ℝ))) =
      (vectorOffDiagonalOuterLaw μ β t a).map vectorOffDiagonalCompletion := by
  change (vectorMeasureOuterLaw (n:=n) μ β t a).map (vectorOffDiagonalCompletion ∘ Prod.fst) = _
  rw [←Measure.map_map measurable_vectorOffDiagonalCompletion measurable_fst,
    vectorMeasureOuterLaw_offDiagonal_marginal μ β t a ht]

theorem vectorMeasureDisorderTilt_removeDiagonal (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) :
    (vectorMeasureDisorderTilt (n:=n) μ β t a).map vectorRemoveDiagonalSample =
      ((vectorOffDiagonalOuterLaw μ β t a).map vectorOffDiagonalCompletion).prod
        (vectorBrownianMeasure n) := by
  haveI := vectorMeasureOuterLaw_probability (n:=n) μ β t a ht
  rw [vectorMeasureDisorderTilt_eq_prod μ β t a ht]
  change ((vectorMeasureOuterLaw μ β t a).prod (vectorBrownianMeasure n)).map
    (Prod.map (fun p : Couplings n×ℝ => (p.1,(0:ℝ))) id) = _
  rw [←Measure.map_prod_map _ _
    (measurable_fst.prodMk measurable_const) measurable_id,Measure.map_id,
    vectorMeasureOuterLaw_removeDiagonal μ β t a ht]

theorem vectorMeasureSpinMean_diagonal_shift (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    vectorMeasureSpinMean μ β t ht q sample =
      vectorMeasureSpinMean μ β t ht q (vectorRemoveDiagonalSample sample) := by
  unfold vectorMeasureSpinMean
  rw [vectorMeasureState_diagonal_shift μ β t ht _
    (by simpa using (Real.toNNReal_le_toNNReal q.property.2)),
    vectorMeasureGradient_diagonal_shift μ β t ht]
  rfl

end QuantitativePaper
