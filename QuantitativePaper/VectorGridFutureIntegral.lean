module
public import QuantitativePaper.VectorFutureGridGeometry
public import QuantitativePaper.VectorDyadicGridLawAgreement
public import QuantitativePaper.VectorFutureMeanSquareLimit
public import QuantitativePaper.VectorFiniteFutureMeanLoss

@[expose] public section

/-! The literal finite future mean-square sum is an integral over the
original profile, using its actual upward-rounding pushforward. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem measurable_vectorMeasureMeanSquareMoment (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (w : Field n)
    (Z : VectorDisorderBrownianSample n → ℝ) (hZ : Measurable Z) :
    Measurable (fun q : Paper.Overlap => ∫p, Z p*(vectorMeasureMeanInDirection μ β t ht q w p)^2
      ∂vectorMeasureDisorderTilt μ β t a) := by
  letI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have hm : Measurable (fun z : Paper.Overlap × VectorDisorderBrownianSample n =>
      vectorMeasureMeanInDirection μ β t ht z.1 w z.2) := by
    unfold vectorMeasureMeanInDirection
    apply Finset.measurable_sum
    intro l _
    exact (((EuclideanSpace.proj l).continuous.measurable.comp
      (measurable_uncurry_vectorMeasureSpinMean μ β t ht)).const_mul (w l))
  exact ((hZ.comp measurable_snd).mul (hm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable

theorem vectorGrid_future_mean_sum_eq_integral (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (j : ℕ) (w : Field n)
    (Z : VectorDisorderBrownianSample n → ℝ) (hZ : Measurable Z) :
    (∑u ∈ Finset.range (vectorDyadicIndex j+3-vectorDyadicTimeIndex q j),
      (observableDepthMass (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) u -
        observableDepthMass (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (u+1)) *
        (∫p, Z p*(vectorBackwardMean (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
          (fun σ => fieldDot w σ) (vectorDyadicIndex j+3-u)
          (vectorFiniteJointState (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht
            ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (vectorDyadicIndex j+3-u)).toNNReal p))^2
          ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a)) =
      vectorDyadicFutureMeanSquareTail μ β t a ht q j w Z := by
  let s := Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let ν := Paper.parisiGridMeasure μ (vectorDyadicIndex j)
  let M := fun r : Paper.Overlap => ∫p, Z p*(vectorMeasureMeanInDirection ν β t ht r w p)^2
    ∂vectorMeasureDisorderTilt ν β t a
  let f := fun r : ℝ => M (projIcc 0 1 zero_le_one r)
  have hP : vectorMeasureDisorderTilt (n:=n) ν β t a = vectorFiniteDisorderTilt s β t a :=
    vectorMeasureDisorderTilt_grid_eq_finite μ j β t a ht
  have hnode (i : ℕ) (hi : i ≤ vectorDyadicIndex j+3) :
      f (s.q i) = ∫p, Z p*(vectorBackwardMean s β t (fun σ => fieldDot w σ) i
        (vectorFiniteJointState s β t ht (s.q i).toNNReal p))^2
        ∂vectorFiniteDisorderTilt s β t a := by
    have hq : projIcc 0 1 zero_le_one (s.q i) =
        (⟨s.q i,s.q_nonneg hi,s.q_le_one hi⟩ : Paper.Overlap) :=
      projIcc_of_mem zero_le_one ⟨s.q_nonneg hi,s.q_le_one hi⟩
    dsimp only [f, M]
    rw [hq, hP]
    apply integral_congr_ae
    exact .of_forall fun p => congrArg (fun x : ℝ => Z p*x^2)
      (vectorMeasureMeanInDirection_grid_node μ β t ht j i hi w p)
  have hsum : (∑u ∈ Finset.range (vectorDyadicIndex j+3-vectorDyadicTimeIndex q j),
      (observableDepthMass s u - observableDepthMass s (u+1)) *
        (∫p, Z p*(vectorBackwardMean s β t (fun σ => fieldDot w σ) (vectorDyadicIndex j+3-u)
          (vectorFiniteJointState s β t ht (s.q (vectorDyadicIndex j+3-u)).toNNReal p))^2
          ∂vectorFiniteDisorderTilt s β t a)) =
      ∫r : Paper.Overlap, if s.q (vectorDyadicTimeIndex q j) < (r:ℝ) then f r else 0
        ∂(Paper.parisiSchemeMeasure s : Measure Paper.Overlap) := by
    rw [←vectorDepthFutureSum_eq_profileIntegral s (vectorDyadicTimeIndex q j)
      (vectorDyadicTimeIndex_le q j)
      (vectorGrid_future_node_order μ (vectorDyadicIndex j) (vectorDyadicTimeIndex q j)
        (by unfold vectorDyadicTimeIndex; omega) (vectorDyadicTimeIndex_le q j)) f]
    apply Finset.sum_congr rfl
    intro u _
    rw [hnode _ (Nat.sub_le _ _)]
  change _ = vectorDyadicFutureMeanSquareTail μ β t a ht q j w Z
  rw [hsum]
  have hm : Measurable M := measurable_vectorMeasureMeanSquareMoment ν β t a ht w Z hZ
  have hf : Measurable (fun r : Paper.Overlap => if s.q (vectorDyadicTimeIndex q j) < (r:ℝ)
      then f r else 0) := by
    have he : (fun r : Paper.Overlap => if s.q (vectorDyadicTimeIndex q j) < (r:ℝ)
        then f r else 0) = fun r : Paper.Overlap =>
          if s.q (vectorDyadicTimeIndex q j) < (r:ℝ) then M r else 0 := by
      funext r
      simp only [f, projIcc_of_mem zero_le_one r.property]
    rw [he]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_subtype_coe) hm measurable_const
  rw [FRSB.parisiSchemeMeasure_grid_eq, Paper.parisiGridMeasure, ProbabilityMeasure.toMeasure_map,
    integral_map_of_stronglyMeasurable (Paper.measurable_parisiGridRound _) hf.stronglyMeasurable]
  unfold vectorDyadicFutureMeanSquareTail
  apply integral_congr_ae
  exact .of_forall fun r => by
    rw [vectorDyadicTimeIndex_node]
    change (if Paper.parisiGridRound (vectorDyadicIndex j) q < Paper.parisiGridRound (vectorDyadicIndex j) r
      then f (Paper.parisiGridRound (vectorDyadicIndex j) r) else 0) = _
    congr 1
    dsimp only [f, M]
    rw [projIcc_of_mem zero_le_one (Paper.parisiGridRound (vectorDyadicIndex j) r).property, hP]
    apply integral_congr_ae
    exact .of_forall fun p => congrArg (fun x : ℝ => Z p*x^2)
      (vectorMeasureMeanInDirection_grid_eq_dyadic μ β t ht r j w p)

end QuantitativePaper
