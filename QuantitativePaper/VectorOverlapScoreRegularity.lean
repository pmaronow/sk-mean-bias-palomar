module
public import QuantitativePaper.VectorMeasureOverlapScore

@[expose] public section

/-! Joint level/sample measurability and actual path continuity of the
marked-spin scores, for deterministic Stieltjes integration. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem measurable_uncurry_vectorMeasureSpinMean (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) :
    Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      vectorMeasureSpinMean μ β t ht z.1 z.2) := by
  have hc : Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      ((z.1 : ℝ).toNNReal,z.2)) :=
    ((continuous_real_toNNReal.measurable.comp measurable_subtype_coe).comp
      measurable_fst).prodMk measurable_snd
  have hX:= (measurable_uncurry_vectorMeasureState (n:=n) μ β t ht).comp hc
  have hz : Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      (z.1,(z.2.1,vectorMeasureState μ β t ht (z.1 : ℝ).toNNReal z.2))) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk hX)
  have hg:= (measurable_vectorMeasureGradient (n:=n) μ β t ht).comp hz
  simpa only [Function.comp_def,Function.uncurry,vectorMeasureSpinMean] using hg

theorem measurable_uncurry_vectorDyadicSpinMean (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (j : ℕ) :
    Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      vectorDyadicSpinMean μ β t ht z.1 j z.2) := by
  have hc : Measurable (fun q : Paper.Overlap=>vectorDyadicTime q j) := by
    unfold vectorDyadicTime
    exact continuous_real_toNNReal.measurable.comp
      (measurable_subtype_coe.comp (Paper.measurable_parisiGridRound _))
  have hX := (measurable_uncurry_vectorFiniteState (n:=n)
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht).comp
      ((hc.comp measurable_fst).prodMk measurable_snd)
  have hz : Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      (Paper.parisiGridRound (vectorDyadicIndex j) z.1,
        (z.2.1,vectorDyadicState μ β t ht j (vectorDyadicTime z.1 j) z.2))) :=
    ((Paper.measurable_parisiGridRound _).comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).prodMk hX)
  have hg := (measurable_vectorFiniteTailGradient (n:=n)
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t).comp hz
  simpa only [Function.comp_def,vectorDyadicSpinMean,vectorDyadicTailGradient] using hg

private theorem measurable_score_pair :
    Measurable (fun z : Field n×Configuration n=>normalizedSpinScore z.1 z.2) := by
  exact measurable_from_prod_countable_left (fun σ=>(continuous_normalizedSpinScore σ).measurable)

theorem measurable_uncurry_vectorMeasureOverlapScore (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) :
    Measurable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      vectorMeasureOverlapScore μ β t ht z.1 z.2) := by
  have hz : Measurable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      (z.1,z.2.1)) := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hm : Measurable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      vectorMeasureSpinMean μ β t ht z.1 z.2.1) :=
    by simpa only [Function.comp_def] using
      (measurable_uncurry_vectorMeasureSpinMean (n:=n) μ β t ht).comp hz
  have hmap : Measurable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      (vectorMeasureSpinMean μ β t ht z.1 z.2.1,z.2.2)) :=
    hm.prodMk (measurable_snd.comp measurable_snd)
  have hh := (measurable_score_pair (n:=n)).comp hmap
  convert hh using 1
  funext z
  rfl

theorem measurable_uncurry_vectorDyadicOverlapScore (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (j : ℕ) :
    Measurable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      vectorDyadicOverlapScore μ β t ht z.1 j z.2) := by
  have hz : Measurable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      (z.1,z.2.1)) := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hm : Measurable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      vectorDyadicSpinMean μ β t ht z.1 j z.2.1) :=
    by simpa only [Function.comp_def] using
      (measurable_uncurry_vectorDyadicSpinMean (n:=n) μ β t ht j).comp hz
  have hmap : Measurable (fun z : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>
      (vectorDyadicSpinMean μ β t ht z.1 j z.2.1,z.2.2)) :=
    hm.prodMk (measurable_snd.comp measurable_snd)
  have hh := (measurable_score_pair (n:=n)).comp hmap
  convert hh using 1
  funext z
  rfl

theorem continuous_vectorMeasureOverlapScore_path (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (p : VectorDisorderBrownianSample n×Configuration n) :
    Continuous (fun q=>vectorMeasureOverlapScore μ β t ht q p) := by
  have hX : Continuous (fun q : Paper.Overlap=>vectorMeasureState μ β t ht (q : ℝ).toNNReal p.1) :=
    (continuous_vectorMeasureState μ β t ht p.1).comp
      (continuous_real_toNNReal.comp continuous_subtype_val)
  have hz : Continuous (fun q : Paper.Overlap=>
      (q,(p.1.1,vectorMeasureState μ β t ht (q : ℝ).toNNReal p.1))) :=
    continuous_id.prodMk (continuous_const.prodMk hX)
  have hg := (continuous_vectorMeasureGradient (n:=n) μ β t ht).comp hz
  exact (continuous_normalizedSpinScore p.2).comp hg

end QuantitativePaper
