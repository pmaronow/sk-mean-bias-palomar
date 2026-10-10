module
public import QuantitativePaper.VectorDyadicDirectionalVariance
public import QuantitativePaper.VectorOverlapScoreRegularity

@[expose] public section

/-! The actual future mean-square integral survives upward profile rounding.
The cutoff atom is excluded at every approximation, not discarded by AE. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem monotone_vectorProfileRound (j : ℕ) : Monotone (Paper.parisiGridRound j) := by
  intro u v huv
  have huv' : (u:ℝ) ≤ (v:ℝ) := huv
  change (Nat.ceil ((j+1:ℕ)*(u:ℝ)):ℝ)/(j+1:ℕ) ≤
    (Nat.ceil ((j+1:ℕ)*(v:ℝ)):ℝ)/(j+1:ℕ)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_left huv' (by positivity : (0:ℝ) ≤ (j+1:ℕ)))

def vectorDyadicFutureMeanSquareTail (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1)
    (q : Paper.Overlap) (j : ℕ) (w : Field n) (Z : VectorDisorderBrownianSample n → ℝ) : ℝ :=
  ∫u : Paper.Overlap,
    if Paper.parisiGridRound (vectorDyadicIndex j) q < Paper.parisiGridRound (vectorDyadicIndex j) u then
      (∫p, Z p*(vectorDyadicMeanInDirection μ β t ht u j w p)^2
        ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a)
    else 0 ∂(μ : Measure Paper.Overlap)

def vectorMeasureFutureMeanSquareTail (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1)
    (q : Paper.Overlap) (w : Field n) (Z : VectorDisorderBrownianSample n → ℝ) : ℝ :=
  ∫u : Paper.Overlap, if q < u then
    (∫p, Z p*(vectorMeasureMeanInDirection μ β t ht u w p)^2
      ∂vectorMeasureDisorderTilt μ β t a) else 0 ∂(μ : Measure Paper.Overlap)

theorem measurable_vectorDyadicMeanSquareMoment (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (j : ℕ) (w : Field n) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable Z) :
    Measurable (fun u : Paper.Overlap => ∫p, Z p*(vectorDyadicMeanInDirection μ β t ht u j w p)^2
      ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a) := by
  letI := vectorFiniteDisorderTilt_probability (n:=n)
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a
  have hm : Measurable (fun z : Paper.Overlap × VectorDisorderBrownianSample n =>
      vectorDyadicMeanInDirection μ β t ht z.1 j w z.2) := by
    unfold vectorDyadicMeanInDirection
    apply Finset.measurable_sum
    intro l _
    exact (((EuclideanSpace.proj l).continuous.measurable.comp
      (measurable_uncurry_vectorDyadicSpinMean μ β t ht j)).const_mul (w l))
  exact ((hZ.comp measurable_snd).mul (hm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable

theorem tendsto_vectorDyadicFutureMeanSquareTail (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (w : Field n) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable Z) (C : ℝ≥0) (hC : ∀p, ‖Z p‖ ≤ C) :
    Tendsto (fun j => vectorDyadicFutureMeanSquareTail μ β t a ht q j w Z) atTop
      (𝓝 (vectorMeasureFutureMeanSquareTail μ β t a ht q w Z)) := by
  let R := vectorDirectionBound w
  have hbound (j : ℕ) (u : Paper.Overlap) :
      |∫p, Z p*(vectorDyadicMeanInDirection μ β t ht u j w p)^2
        ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a| ≤
        (C:ℝ)*R^2 := by
    letI := vectorFiniteDisorderTilt_probability (n:=n)
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a
    have hb p : ‖Z p*(vectorDyadicMeanInDirection μ β t ht u j w p)^2‖ ≤ (C:ℝ)*R^2 := by
      simp only [norm_mul, Real.norm_eq_abs, abs_sq]
      have hm := pow_le_pow_left₀ (abs_nonneg (vectorDyadicMeanInDirection μ β t ht u j w p))
        (vectorDyadicMeanInDirection_bound μ β t ht u j w p) 2
      have hm' : (vectorDyadicMeanInDirection μ β t ht u j w p)^2 ≤ R^2 := by
        simpa only [sq_abs] using hm
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hC p) hm' (sq_nonneg _) C.coe_nonneg
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const
        (μ:=vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a)
        (.of_forall hb))
  unfold vectorDyadicFutureMeanSquareTail vectorMeasureFutureMeanSquareTail
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (C:ℝ)*R^2)
  · exact .of_forall fun j => (Measurable.ite
      (measurableSet_lt measurable_const (Paper.measurable_parisiGridRound _))
      (measurable_vectorDyadicMeanSquareMoment μ β t a ht j w Z hZ) measurable_const).aestronglyMeasurable
  · exact .of_forall fun j => .of_forall fun u => by
      split_ifs
      · simpa only [Real.norm_eq_abs] using hbound j u
      · simp only [norm_zero]
        exact mul_nonneg C.coe_nonneg (sq_nonneg _)
  · exact integrable_const _
  · exact .of_forall fun u => by
      by_cases hqu : q < u
      · rw [ite_eq_left hqu]
        have hq : Tendsto (fun j => (Paper.parisiGridRound (vectorDyadicIndex j) q:ℝ)) atTop (𝓝 (q:ℝ)) :=
          continuous_subtype_val.tendsto q |>.comp ((Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex)
        have hu : Tendsto (fun j => (Paper.parisiGridRound (vectorDyadicIndex j) u:ℝ)) atTop (𝓝 (u:ℝ)) :=
          continuous_subtype_val.tendsto u |>.comp ((Paper.tendsto_parisiGridRound u).comp tendsto_vectorDyadicIndex)
        have hg : (0:ℝ) < (u:ℝ)-q := sub_pos.mpr hqu
        have he : ∀ᶠj in atTop,
            Paper.parisiGridRound (vectorDyadicIndex j) q < Paper.parisiGridRound (vectorDyadicIndex j) u :=
          ((hu.sub hq).eventually (eventually_gt_nhds hg)).mono fun j hj =>
            (show (Paper.parisiGridRound (vectorDyadicIndex j) q:ℝ) <
              (Paper.parisiGridRound (vectorDyadicIndex j) u:ℝ) from sub_pos.mp hj)
        apply (tendsto_integral_vectorDyadicTilt_mean_square μ β t a ht u w Z hZ C hC).congr'
        filter_upwards [he] with j hj
        simp only [ite_eq_left hj]
      · have he (j : ℕ) : ¬Paper.parisiGridRound (vectorDyadicIndex j) q <
            Paper.parisiGridRound (vectorDyadicIndex j) u :=
          not_lt_of_ge (monotone_vectorProfileRound _ (not_lt.mp hqu))
        simp only [ite_eq_right hqu, ite_eq_right (he _)]
        exact tendsto_const_nhds

end QuantitativePaper
