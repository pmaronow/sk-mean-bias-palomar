module
public import QuantitativePaper.VectorMatrixMeanCross
public import QuantitativePaper.VectorMeasureGradientRemainder
public import FourPapersCommon.HilbertL2Integrals

@[expose] public section

/-! Literal spin-mean Brownian integrands, their square integrability, and
the quantitative local cross error obtained from the genuine gradient Taylor
remainder and exact Gaussian moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ENNReal Topology BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def vectorMeanBrownianIntegrand (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) : Field n→L[ℝ]Field n :=
  Real.sqrt ((1-t)*β^2) • vectorMeasureHessianProcess μ β t ht q sample

theorem adapted_vectorMeanBrownianIntegrand (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] (vectorMeanBrownianIntegrand (n:=n) μ β t ht q) := by
  convert (adapted_vectorMeasureHessianProcess (n:=n) μ β t ht q).const_smul
    (Real.sqrt ((1-t)*β^2)) using 1
  funext sample
  rfl

theorem norm_vectorMeanBrownianIntegrand_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeanBrownianIntegrand μ β t ht q sample‖≤Real.sqrt ((1-t)*β^2)*(n:ℝ) := by
  rw [vectorMeanBrownianIntegrand, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (norm_vectorMeasureHessianProcess_le μ β t ht q sample) (Real.sqrt_nonneg _)

theorem vectorHessianHilbertSquare_smul (α : ℝ) (H : Field n→L[ℝ]Field n) :
    vectorHessianHilbertSquare (α • H)=α^2*vectorHessianHilbertSquare H := by
  simp only [vectorHessianHilbertSquare, ContinuousLinearMap.smul_apply, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]

theorem vectorMeanBrownianIntegrand_hilbertSquare (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    vectorHessianHilbertSquare (vectorMeanBrownianIntegrand μ β t ht q sample)=
      ((1-t)*β^2)*vectorMeasureHessianEnergy μ β t ht q sample := by
  rw [vectorMeanBrownianIntegrand, vectorHessianHilbertSquare_smul,
    Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β))]
  rfl

theorem memLp_vectorMeasureSpinMean (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    MemLp (vectorMeasureSpinMean (n:=n) μ β t ht q) 2 (vectorMeasureDisorderTilt μ β t a) := by
  have := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  exact MemLp.of_bound ((adapted_vectorMeasureSpinMean μ β t ht q).mono
    ((vectorBrownianFiltration n).le _) le_rfl).aestronglyMeasurable (Real.sqrt n)
    (.of_forall fun sample => norm_vectorMeasureGradient_le μ β t ht q sample.1 _)

theorem memLp_vectorMeanBrownianLocalTerm (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (r q : Paper.Overlap) (hrq : r≤q) :
    MemLp (fun sample : VectorDisorderBrownianSample n => vectorMeanBrownianIntegrand μ β t ht r sample
      (disorderVectorBrownianIncrement (r:ℝ).toNNReal (q:ℝ).toNNReal sample)) 2
        (vectorMeasureDisorderTilt μ β t a) := by
  have hB : MemLp (disorderVectorBrownianIncrement (n:=n) (r:ℝ).toNNReal (q:ℝ).toNNReal) 2
      (vectorMeasureDisorderTilt μ β t a) :=
    (memLp_two_iff_integrable_sq_norm (measurable_disorderVectorBrownianIncrement _ _).aestronglyMeasurable).mpr
      (integrable_tilted_increment_norm_pow μ β t a ht _ _ (Real.toNNReal_mono hrq) 2)
  have hH : AEStronglyMeasurable (vectorMeanBrownianIntegrand (n:=n) μ β t ht r)
      (vectorMeasureDisorderTilt μ β t a) := ((adapted_vectorMeanBrownianIntegrand μ β t ht r).mono
    ((vectorBrownianFiltration n).le _) le_rfl).aestronglyMeasurable
  apply hB.of_le_mul ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hH.prodMk hB.aestronglyMeasurable))
  exact .of_forall fun sample => ((vectorMeanBrownianIntegrand μ β t ht r sample).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (norm_vectorMeanBrownianIntegrand_le μ β t ht r sample) (norm_nonneg _))

def vectorMeanCrossErrorConstant (n : ℕ) (β t : ℝ) : ℝ :=
  vectorGradientStochasticRemainderConstant n β t*Real.sqrt ((1-t)*β^2)*(n:ℝ)*
    (vectorGaussianNormMoment n 1+vectorGaussianNormMoment n 3)

theorem vectorMean_cross_cell_bound (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q) :
    ‖(∫sample : VectorDisorderBrownianSample n,inner ℝ (vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample)
      (vectorMeanBrownianIntegrand μ β t ht.le r sample
        (disorderVectorBrownianIncrement (r:ℝ).toNNReal (q:ℝ).toNNReal sample)) ∂vectorMeasureDisorderTilt (n:=n) μ β t a)-
      (∫sample : VectorDisorderBrownianSample n,‖vectorMeanBrownianIntegrand μ β t ht.le r sample
        (disorderVectorBrownianIncrement (r:ℝ).toNNReal (q:ℝ).toNNReal sample)‖^2 ∂vectorMeasureDisorderTilt μ β t a)‖≤
      vectorMeanCrossErrorConstant n β t*((q:ℝ)-r)*Real.sqrt ((q:ℝ)-r) := by
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  have := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  let D : VectorDisorderBrownianSample n→Field n := fun sample => vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample
  let B := disorderVectorBrownianIncrement (n:=n) (r:ℝ).toNNReal (q:ℝ).toNNReal
  let A := fun sample => vectorMeanBrownianIntegrand μ β t ht.le r sample (B sample)
  let d : ℝ := (q:ℝ)-r
  let K := vectorGradientStochasticRemainderConstant n β t
  let L := Real.sqrt ((1-t)*β^2)*(n:ℝ)
  have hd : 0≤d := sub_nonneg.mpr hrq
  have hK : 0≤K := vectorGradientStochasticRemainderConstant_nonneg β t ht.le
  have hL : 0≤L := mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg n)
  have hD : MemLp D 2 P := (memLp_vectorMeasureSpinMean μ β t a ht.le q).sub (memLp_vectorMeasureSpinMean μ β t a ht.le r)
  have hA : MemLp A 2 P := memLp_vectorMeanBrownianLocalTerm μ β t a ht.le r q hrq
  have hDA : Integrable (fun sample => inner ℝ (D sample) (A sample)) P := integrable_inner_of_memLp_two hD hA
  have hA2 : Integrable (fun sample => ‖A sample‖^2) P := hA.integrable_norm_pow'
  have he : (∫sample,inner ℝ (D sample) (A sample)∂P)-(∫sample,‖A sample‖^2∂P)=
      ∫sample,inner ℝ (D sample-A sample) (A sample)∂P := by
    rw [←integral_sub hDA hA2]
    apply integral_congr_ae
    exact .of_forall fun sample => by
      change inner ℝ (D sample) (A sample)-‖A sample‖^2=inner ℝ (D sample-A sample) (A sample)
      simpa only [real_inner_self_eq_norm_sq] using
        (inner_sub_left (𝕜:=ℝ) (D sample) (A sample) (A sample)).symm
  change ‖(∫sample,inner ℝ (D sample) (A sample)∂P)-(∫sample,‖A sample‖^2∂P)‖≤_
  rw [he]
  have h1 : Integrable (fun sample => ‖B sample‖) P := by
    simpa only [pow_one] using integrable_tilted_increment_norm_pow μ β t a ht.le _ _ (Real.toNNReal_mono hrq) 1
  have h3 : Integrable (fun sample => ‖B sample‖^3) P :=
    integrable_tilted_increment_norm_pow μ β t a ht.le _ _ (Real.toNNReal_mono hrq) 3
  have hi := ((h1.const_mul d).add h3).const_mul (K*L)
  have hn := norm_integral_le_of_norm_le hi (.of_forall fun sample => by
    have hrem := vectorMeasureSpinMean_increment_remainder μ β t hβ ht r q hrq sample
    change ‖D sample-A sample‖≤K*(d+‖B sample‖^2) at hrem
    have hAb : ‖A sample‖≤L*‖B sample‖ :=
      ((vectorMeanBrownianIntegrand μ β t ht.le r sample).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_vectorMeanBrownianIntegrand_le μ β t ht.le r sample) (norm_nonneg _))
    calc
      ‖inner ℝ (D sample-A sample) (A sample)‖≤‖D sample-A sample‖*‖A sample‖ := by
        simpa only [Real.norm_eq_abs] using abs_real_inner_le_norm (D sample-A sample) (A sample)
      _≤(K*(d+‖B sample‖^2))*(L*‖B sample‖) :=
        mul_le_mul hrem hAb (norm_nonneg _) (mul_nonneg hK (add_nonneg hd (sq_nonneg _)))
      _=K*L*(d*‖B sample‖+‖B sample‖^3) := by ring)
  apply hn.trans_eq
  rw [integral_const_mul]
  change K*L*(∫sample,d*‖B sample‖+‖B sample‖^3∂P)=_
  have ha := integral_add (h1.const_mul d) h3
  rw [ha,integral_const_mul]
  have hclock : ((q:ℝ).toNNReal:ℝ)-((r:ℝ).toNNReal:ℝ)=d := by
    rw [Real.coe_toNNReal _ q.property.1,Real.coe_toNNReal _ r.property.1]
  have h1eq : (∫sample,‖B sample‖∂P)=Real.sqrt d*vectorGaussianNormMoment n 1 := by
    simpa only [B,P,pow_one,hclock] using integral_tilted_increment_norm_pow μ β t a ht.le
      (r:ℝ).toNNReal (q:ℝ).toNNReal (Real.toNNReal_mono hrq) 1
  have h3eq : (∫sample,‖B sample‖^3∂P)=Real.sqrt d^3*vectorGaussianNormMoment n 3 := by
    simpa only [B,P,hclock] using integral_tilted_increment_norm_pow μ β t a ht.le
      (r:ℝ).toNNReal (q:ℝ).toNNReal (Real.toNNReal_mono hrq) 3
  rw [h1eq,h3eq]
  rw [show Real.sqrt d^3=d*Real.sqrt d from by
    calc Real.sqrt d^3=Real.sqrt d^2*Real.sqrt d := by ring
         _=d*Real.sqrt d := by rw [Real.sq_sqrt hd]]
  dsimp only [K,L,d,vectorMeanCrossErrorConstant]
  ring

end QuantitativePaper
