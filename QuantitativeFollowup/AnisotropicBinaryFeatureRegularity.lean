module
public import QuantitativeFollowup.AnisotropicBinaryFeatureSquareKernel

@[expose] public section

/-! Honest bounded adapted pair-feature second response and jointly
measurable raw future squares for the native arbitrary-profile process. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

theorem measurable_uncurry_anisotropicProcessPairResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (e : AnisotropicCouplingIndex n) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      anisotropicProcessPairResponse D μ z.1 e z.2) := by
  have h:=(continuous_anisotropicTailPairResponse_joint D μ e).measurable.comp
    (measurable_fst.prodMk (measurable_uncurry_anisotropicProcessParameter D μ))
  simpa only [Function.comp_def,anisotropicProcessPairResponse] using h

theorem adapted_anisotropicProcessPairSecond (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] (anisotropicProcessPairSecond D μ q e) := by
  have h:=(continuous_anisotropicTailPairSecond_joint D μ e).measurable.comp
    ((measurable_const (a:=q)).prodMk (adapted_anisotropicProcessParameter D μ q))
  unfold anisotropicProcessPairSecond
  simpa only [Function.comp_def] using h

theorem norm_anisotropicProcessPairSecond_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n)
    (sample : AnisotropicDisorderBrownianSample n) :
    ‖anisotropicProcessPairSecond D μ q e sample‖ ≤ anisotropicPairSecondBound D e := by
  apply le_of_tendsto ((tendsto_anisotropicProcessPairSecond_moving D μ sample e
    (tendsto_const_nhds (x:=q))).norm)
  exact .of_forall fun j=>norm_anisotropicFiniteTailPairSecond_le D _ q _ e

def anisotropicRawFuturePairSquare (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  ∫r : Paper.Overlap,if q < r then (anisotropicProcessPairResponse D μ r e sample)^2 else 0
    ∂(μ:Measure Paper.Overlap)

theorem measurable_anisotropicRawFuturePairSquare (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    Measurable (anisotropicRawFuturePairSquare D μ q e) := by
  classical
  unfold anisotropicRawFuturePairSquare
  have hset : MeasurableSet {z : Paper.Overlap×AnisotropicDisorderBrownianSample n|q < z.1}:=
    measurableSet_lt (measurable_const (a:=q)) measurable_fst
  have hF : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      if q < z.1 then (anisotropicProcessPairResponse D μ z.1 e z.2)^2 else 0) :=
    Measurable.ite hset ((measurable_uncurry_anisotropicProcessPairResponse D μ e).pow_const 2) measurable_const
  exact (hF.stronglyMeasurable.integral_prod_left' (μ:=(μ:Measure Paper.Overlap))).measurable

theorem norm_anisotropicRawFuturePairSquare_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n)
    (sample : AnisotropicDisorderBrownianSample n) :
    ‖anisotropicRawFuturePairSquare D μ q e sample‖ ≤ 1 := by
  unfold anisotropicRawFuturePairSquare
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=(μ:Measure Paper.Overlap))
    (C:=1) (.of_forall fun r=>by
      split_ifs
      · rw [norm_pow]
        exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicProcessPairResponse_bound D μ r e sample) 2).trans_eq (by norm_num)
      · simp only [norm_zero,zero_le_one])

theorem anisotropicRawFuturePairSquare_fixed_disorder_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (e : AnisotropicCouplingIndex n) (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable Z) (hZi : Integrable Z (vectorDisorderBrownianMeasure n)) :
    (∫p,Z p*anisotropicRawFuturePairSquare D μ q e (g,p.2) ∂vectorDisorderBrownianMeasure n)=
      anisotropicFuturePairSquareMoment D μ g q e Z := by
  classical
  let F:=fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
    Z z.2*(if q < z.1 then (anisotropicProcessPairResponse D μ z.1 e (g,z.2.2))^2 else 0)
  have hmap : Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>(z.1,(g,z.2.2))) :=
    measurable_fst.prodMk ((measurable_const (a:=g)).prodMk measurable_snd.snd)
  have hM:=(measurable_uncurry_anisotropicProcessPairResponse D μ e).comp hmap
  have hset : MeasurableSet {z : Paper.Overlap×VectorDisorderBrownianSample n|q < z.1}:=
    measurableSet_lt (measurable_const (a:=q)) measurable_fst
  have hM' : Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      anisotropicProcessPairResponse D μ z.1 e (g,z.2.2)) := by
    simpa only [Function.comp_def] using hM
  have hC : Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      if q < z.1 then (anisotropicProcessPairResponse D μ z.1 e (g,z.2.2))^2 else 0) :=
    Measurable.ite hset (hM'.pow_const 2) measurable_const
  have hF : Measurable F := (hZ.comp measurable_snd).mul hC
  have hi : Integrable F ((μ:Measure Paper.Overlap).prod (vectorDisorderBrownianMeasure n)) :=
    (hZi.norm.comp_snd (μ:Measure Paper.Overlap)).mono' hF.aestronglyMeasurable (.of_forall fun z=>by
      dsimp only [F]
      rw [norm_mul]
      apply (mul_le_mul_of_nonneg_left (show ‖if q < z.1 then
        (anisotropicProcessPairResponse D μ z.1 e (g,z.2.2))^2 else 0‖ ≤ 1 from ?_)
        (norm_nonneg (Z z.2))).trans_eq (mul_one _)
      split_ifs
      · rw [norm_pow]
        exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicProcessPairResponse_bound D μ z.1 e _) 2).trans_eq (by norm_num)
      · simp)
  calc
    _ = ∫p,(∫r : Paper.Overlap,F (r,p) ∂(μ:Measure Paper.Overlap)) ∂vectorDisorderBrownianMeasure n := by
      apply integral_congr_ae
      exact .of_forall fun p=>(integral_const_mul (Z p) _).symm
    _ = ∫r : Paper.Overlap,(∫p,F (r,p) ∂vectorDisorderBrownianMeasure n) ∂(μ:Measure Paper.Overlap) :=
      (integral_integral_swap hi).symm
    _ = _ := by
      unfold anisotropicFuturePairSquareMoment anisotropicPairSquareMoment
      apply integral_congr_ae
      exact .of_forall fun r=>by
        by_cases hqr:q < r
        · simp only [F,ite_eq_left hqr]
        · simp only [F,ite_eq_right hqr,mul_zero,integral_zero]

end QuantitativeFollowup
