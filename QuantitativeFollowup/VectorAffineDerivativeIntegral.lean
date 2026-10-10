module
public import QuantitativePaper.VectorFractionalVariation
public import FourPapersCommon.BoundedTimeFubini

@[expose] public section

/-! The literal affine-control derivative is its actual integrated
linear terminal pairing minus the quadratic control cost. -/
noncomputable section
open Set MeasureTheory QuantitativePaper StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorAffineControlDerivative_eq_time_integral (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (sample : VectorDisorderBrownianSample n) :
    vectorAffineControlDerivative μ ν β t A 0 sample=
      ∫r in Ioc 0 1,((1-t)*β^2)*(Paper.parisiCDF ν r-Paper.parisiCDF μ r)*
        (inner ℝ (vectorTerminalGradient n β t sample.1
          (vectorControlledState ((1-t)*β^2) μ A 1 sample)) (A r sample)-‖A r sample‖^2/2)
        ∂nonnegativeLebesgueMeasure := by
  let c:=(1-t)*β^2
  let v:=vectorTerminalGradient n β t sample.1 (vectorControlledState c μ A 1 sample)
  have hd (ρ : Paper.ParisiMeasure) : IntegrableOn (fun r=>vectorControlDrift c ρ A r sample)
      (Ioc 0 1) nonnegativeLebesgueMeasure:=by
    apply integrableOn_bounded_vector_drift _ (measurable_vectorControlDrift c ρ A hA).of_uncurry_right
      (|c| *Real.sqrt (n:ℝ)).toNNReal
    · intro r
      rw [Real.coe_toNNReal _ (by positivity)]
      exact norm_vectorControlDrift_le c ρ A hA r sample
  have hc (ρ : Paper.ParisiMeasure) := integrableOn_vectorParisiControlCost c ρ A hA sample
  have hL := (innerSL ℝ v).integral_comp_comm ((hd ν).sub (hd μ))
  simp only [innerSL_apply_apply,Pi.sub_apply] at hL
  have hi : IntegrableOn (fun r=>inner ℝ v (vectorControlDrift c ν A r sample-
      vectorControlDrift c μ A r sample)) (Ioc 0 1) nonnegativeLebesgueMeasure :=
    (innerSL ℝ v).integrable_comp ((hd ν).sub (hd μ))
  have he : vectorControlledState c ν A 1 sample-vectorControlledState c μ A 1 sample=
      ∫r in Ioc 0 1,vectorControlDrift c ν A r sample-vectorControlDrift c μ A r sample
        ∂nonnegativeLebesgueMeasure := by
    simp only [vectorControlledState,add_sub_add_left_eq_sub,vectorIntegratedDrift]
    exact (integral_sub (hd ν) (hd μ)).symm
  dsimp only [vectorAffineControlDerivative]
  simp only [zero_smul,add_zero]
  change inner ℝ v (vectorControlledState c ν A 1 sample-vectorControlledState c μ A 1 sample)-
    (vectorParisiControlIntegratedCost c ν A sample-vectorParisiControlIntegratedCost c μ A sample)=_
  rw [he,←hL,vectorParisiControlIntegratedCost,vectorParisiControlIntegratedCost,
    ←integral_sub (hc ν) (hc μ),←integral_sub (f:=fun r=>inner ℝ v (vectorControlDrift c ν A r sample-vectorControlDrift c μ A r sample)) (g:=fun r=>vectorParisiControlCost c ν A r sample-vectorParisiControlCost c μ A r sample) hi ((hc ν).sub (hc μ))]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r _
  simp only [vectorControlDrift,inner_sub_right,inner_smul_right,
    vectorParisiControlCost]
  dsimp only [c,v]
  ring

end QuantitativeFollowup
