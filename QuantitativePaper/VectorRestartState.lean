module
public import QuantitativePaper.VectorMeasureIto

@[expose] public section

/-! The actual arbitrary-profile diffusion restarted at a fixed physical time,
with a fixed disorder realization and an arbitrary initial field. The Wiener
clock is elapsed time; the otherwise retained initial disorder is ignored. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorFixedRestartDriftData (d : VectorAdditiveDriftData n)
    (q : ℝ≥0) (p : Couplings n × ℝ) : VectorAdditiveDriftData n where
  drift r _ x := d.drift (q+r) p x
  bound := d.bound
  spatialLip := d.spatialLip
  measurable := by
    let insert : ℝ≥0×((Couplings n×ℝ)×Field n)→ℝ≥0×((Couplings n×ℝ)×Field n) :=
      fun z=>(q+z.1,(p,z.2.2))
    have hi : Measurable insert:=by unfold insert; fun_prop
    have hm:=d.measurable.comp hi
    dsimp only [Function.comp_def,insert] at hm
    exact hm
  norm_le r _ x := d.norm_le _ p x
  lipschitz r _ := d.lipschitz _ p

def vectorRestartDriftData (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (q : Paper.Overlap) (p : Couplings n × ℝ) : VectorAdditiveDriftData n :=
  vectorFixedRestartDriftData (vectorMeasureDriftData μ β t ht) (q:ℝ).toNNReal p

def vectorRestartHorizon (q : Paper.Overlap) : ℝ≥0 := (1-(q:ℝ)).toNNReal

def vectorRestartState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (q : Paper.Overlap) (p : Couplings n × ℝ) (x : Field n)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : Field n :=
  vectorAdditiveState (vectorRestartDriftData μ β t ht q p)
    (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q) r sample

theorem continuous_vectorRestartState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (q : Paper.Overlap) (p : Couplings n × ℝ) (x : Field n)
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r=>vectorRestartState μ β t ht q p x r sample) :=
  continuous_vectorAdditiveState _ _ _ _ _

theorem measurable_uncurry_vectorRestartState (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) (x : Field n) :
    Measurable (Function.uncurry (vectorRestartState μ β t ht q p x)) :=
  measurable_uncurry_vectorAdditiveState _ _ _ _

theorem stronglyAdapted_vectorRestartState (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) (x : Field n) :
    StronglyAdapted (vectorBrownianFiltration n) (vectorRestartState μ β t ht q p x) :=
  stronglyAdapted_vectorAdditiveState _ _ _ _

@[simp] theorem vectorRestartState_zero (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) (x : Field n)
    (sample : VectorDisorderBrownianSample n) :
    vectorRestartState μ β t ht q p x 0 sample=x :=
  vectorAdditiveState_zero _ _ _ _ _

theorem vectorRestartState_equation (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (q : Paper.Overlap) (p : Couplings n × ℝ) (x : Field n)
    (r : ℝ≥0) (hr : r ≤ vectorRestartHorizon q)
    (sample : VectorDisorderBrownianSample n) :
    vectorRestartState μ β t ht q p x r sample=x+
      Real.sqrt ((1-t)*β^2) • disorderVectorBrownian r sample+
      ∫ s in (0:ℝ)..(r:ℝ),
        ((1-t)*β^2*Paper.parisiCDF μ ((q:ℝ)+s)) •
          vectorMeasureGradient μ β t (projIcc (0:ℝ) 1 zero_le_one ((q:ℝ)+s)) p
            (vectorRestartState μ β t ht q p x s.toNNReal sample) := by
  have he:=vectorAdditiveState_equation (vectorRestartDriftData μ β t ht q p)
    (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q) r hr sample
  change vectorRestartState μ β t ht q p x r sample=x+_+_ at he
  refine he.trans ?_
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le r.coe_nonneg] at hs
  change ((1-t)*β^2*Paper.parisiCDF μ
    (((q:ℝ).toNNReal:ℝ)+(s.toNNReal:ℝ))) •
      vectorMeasureGradient μ β t
        (projIcc (0:ℝ) 1 zero_le_one (((q:ℝ).toNNReal:ℝ)+(s.toNNReal:ℝ))) p
        (vectorRestartState μ β t ht q p x s.toNNReal sample)=_
  rw [Real.coe_toNNReal (q:ℝ) q.property.1,Real.coe_toNNReal s hs.1]

theorem vectorItoCharacteristics_vectorRestartState (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) (x : Field n) :
    VectorItoCharacteristics (vectorRestartState μ β t ht q p x)
      (vectorAdditiveDrift (vectorRestartDriftData μ β t ht q p)
        (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q))
      (Real.sqrt ((1-t)*β^2)) :=
  vectorItoCharacteristics_vectorAdditiveState _ _ _ _

end QuantitativePaper
