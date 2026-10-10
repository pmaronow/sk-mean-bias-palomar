module
public import QuantitativePaper.VectorItoGenerator
public import FourPapersCommon.VectorSquareCalculus
public import FourPapersCommon.TimeFTCSquare

@[expose] public section

/-! Squared actual spatial tests and their genuine vector generator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorBilinearTrace_square (f : Field n→ℝ) (hf : ContDiff ℝ 2 f) (x : Field n) :
    vectorBilinearTrace (vectorHessian (fun y=>f y^2) x)=
      2*f x*vectorBilinearTrace (vectorHessian f x)+
        2*∑l : Fin n,(fderiv ℝ f x (EuclideanSpace.single l 1))^2 := by
  unfold vectorBilinearTrace
  simp_rw [vectorHessian_square_apply f hf,pow_two]
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  congr 1
  simpa only [mul_assoc] using (Finset.mul_sum Finset.univ
    (fun l : Fin n=>fderiv ℝ f x (EuclideanSpace.single l 1)*fderiv ℝ f x (EuclideanSpace.single l 1)) (2 : ℝ)).symm

def VectorSpatialItoTest.square
    {f : ℝ≥0→VectorDisorderBrownianSample n→Field n→ℝ}
    {X : ℝ≥0→VectorDisorderBrownianSample n→Field n}
    (hf : VectorSpatialItoTest f X) (R : ℝ≥0)
    (hR : ∀q sample x,‖f q sample x‖≤R)
    (ha : ∀q r,Measurable[vectorBrownianFiltration n r] (fun sample=>f q sample (X r sample)))
    (hc : ∀sample,Continuous (fun q=>f q sample (X q sample))) :
    VectorSpatialItoTest (fun q sample x=>f q sample x^2) X := by
  let M : ℝ≥0:=R+hf.firstBound+hf.secondBound+hf.thirdBound
  have hMR : (R : ℝ)≤M := by
    dsimp [M]
    linarith [hf.firstBound.coe_nonneg,hf.secondBound.coe_nonneg,hf.thirdBound.coe_nonneg]
  have hM1 : (hf.firstBound : ℝ)≤M := by
    dsimp [M]
    linarith [R.coe_nonneg,hf.secondBound.coe_nonneg,hf.thirdBound.coe_nonneg]
  have hM2 : (hf.secondBound : ℝ)≤M := by
    dsimp [M]
    linarith [R.coe_nonneg,hf.firstBound.coe_nonneg,hf.thirdBound.coe_nonneg]
  have hM3 : (hf.thirdBound : ℝ)≤M := by
    dsimp [M]
    linarith [R.coe_nonneg,hf.firstBound.coe_nonneg,hf.secondBound.coe_nonneg]
  have hjet (q : ℝ≥0) (sample : VectorDisorderBrownianSample n) (j : ℕ) (hj : j≤3)
      (x : Field n) : ‖iteratedFDeriv ℝ j (f q sample) x‖≤M := by
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]
      exact (hR q sample x).trans hMR
    · rw [norm_iteratedFDeriv_one]
      exact (hf.first_le q sample x).trans hM1
    · exact (hf.second_le q sample x).trans hM2
    · exact (hf.third_le q sample x).trans hM3
  refine {
    firstBound := 2*M^2
    secondBound := 4*M^2
    thirdBound := 8*M^2
    measurable := fun q=>(hf.measurable q).pow_const 2
    regularity := fun q sample=>(hf.regularity q sample).pow 2
    first_le := ?_
    second_le := ?_
    third_le := ?_
    adapted_first := ?_
    adapted_second := ?_
    continuous_first_path := ?_
    continuous_trace_path := ?_ }
  · intro q sample x
    rw [←norm_iteratedFDeriv_one]
    simpa only [pow_one,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat] using
      norm_iteratedFDeriv_square_le _ (hf.regularity q sample) M M.coe_nonneg (hjet q sample) 1 (by norm_num) x
  · intro q sample x
    simpa only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat,show (2 : ℝ)^2=4 by norm_num] using
      norm_iteratedFDeriv_square_le _ (hf.regularity q sample) M M.coe_nonneg (hjet q sample) 2 (by norm_num) x
  · intro q sample x
    simpa only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat,show (2 : ℝ)^3=8 by norm_num] using
      norm_iteratedFDeriv_square_le _ (hf.regularity q sample) M M.coe_nonneg (hjet q sample) 3 le_rfl x
  · intro q r
    simp_rw [fderiv_square _ ((hf.regularity q _).differentiable (by norm_num))]
    exact (measurable_const.mul (ha q r)).smul (hf.adapted_first q r)
  · intro q r
    simp_rw [vectorHessian_square _ ((hf.regularity q _).of_le (by norm_num))]
    have hm : Measurable (fun z : (Field n→L[ℝ]ℝ)×(Field n→L[ℝ]ℝ)=>z.1.smulRight z.2) :=
      (isBoundedBilinearMap_smulRight (𝕜:=ℝ) (E:=Field n) (F:=Field n→L[ℝ]ℝ)).continuous.measurable
    exact ((ha q r).smul (hf.adapted_second q r) |>.add
      (hm.comp ((hf.adapted_first q r).prodMk (hf.adapted_first q r)))).const_smul (2 : ℝ)
  · intro sample
    simp_rw [fderiv_square _ ((hf.regularity _ sample).differentiable (by norm_num))]
    exact ((hc sample).const_mul 2).smul (hf.continuous_first_path sample)
  · intro sample
    simp_rw [vectorBilinearTrace_square _ ((hf.regularity _ sample).of_le (by norm_num))]
    apply (((hc sample).const_mul 2).mul (hf.continuous_trace_path sample)).add
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro l _
    exact (((hf.continuous_first_path sample).clm_apply continuous_const).pow 2)

theorem vectorItoGenerator_square {T : ℝ≥0}
    (test : TimeFTCData (VectorDisorderBrownianSample n) (Field n) T)
    (R L : ℝ≥0) (hR : ∀r sample x,‖test.f r sample x‖≤R)
    (hL : ∀r sample,LipschitzWith L (test.f r sample))
    (htc : ∀sample,Continuous (fun z : ℝ×Field n=>test.f z.1 sample z.2))
    (hreg : ∀r sample,ContDiff ℝ 2 (test.f r sample))
    (X d : ℝ≥0→VectorDisorderBrownianSample n→Field n) (σ : ℝ)
    (q : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    vectorItoGenerator (test.square R L hR hL htc) X d σ q sample=
      2*test.f q sample (X q sample)*vectorItoGenerator test X d σ q sample+
        σ^2*∑l : Fin n,(fderiv ℝ (test.f q sample) (X q sample) (EuclideanSpace.single l 1))^2 := by
  unfold vectorItoGenerator
  change fderiv ℝ (fun x=>test.f q sample x^2) (X q sample) (d q sample)+
    σ^2/2*vectorBilinearTrace (vectorHessian (fun x=>test.f q sample x^2) (X q sample))+
    2*test.f q sample (X q sample)*test.ft q sample (X q sample)=_
  rw [fderiv_square _ ((hreg q sample).differentiable (by norm_num)),
    vectorBilinearTrace_square _ (hreg q sample)]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

end QuantitativePaper
