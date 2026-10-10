module
public import QuantitativePaper.VectorBrownianMoments
public import FourPapersCommon.VectorCubicBounds

@[expose] public section

/-! The actual spatial Taylor remainder against genuine Wiener increments is
integrable and has the mesh-decaying bound used in the vector expectation
formula. Sample-dependent test functions permit independent initial disorder.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ContDiff
namespace QuantitativePaper
open FourPapersCommon

def vectorSpatialTaylorError {n : ℕ}
    (f : VectorDisorderBrownianSample n → Field n → ℝ)
    (X W V : VectorDisorderBrownianSample n → Field n)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  f sample (X sample+W sample+V sample)-
    vectorNoiseDriftTaylorPolynomial (f sample) (X sample) (W sample) (V sample)

theorem integral_weighted_vectorSpatialTaylorError_bound {n : ℕ}
    (r t : ℝ≥0) (hrt : r ≤ t) (σ : ℝ)
    (f : VectorDisorderBrownianSample n → Field n → ℝ)
    (hf : ∀ sample,ContDiff ℝ 3 (f sample))
    (K₂ K₃ D : ℝ≥0)
    (h₂ : ∀ sample x,‖iteratedFDeriv ℝ 2 (f sample) x‖ ≤ K₂)
    (h₃ : ∀ sample x,‖iteratedFDeriv ℝ 3 (f sample) x‖ ≤ K₃)
    (X V : VectorDisorderBrownianSample n → Field n)
    (hV : ∀ sample,‖V sample‖ ≤ D*((t : ℝ)-r))
    (Z : VectorDisorderBrownianSample n → ℝ) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖ ≤ C)
    (hR : AEStronglyMeasurable (fun sample=>Z sample*vectorSpatialTaylorError f X
      (fun sample=>σ • disorderVectorBrownianIncrement r t sample) V sample)
      (vectorDisorderBrownianMeasure n)) :
    Integrable (fun sample=>Z sample*vectorSpatialTaylorError f X
      (fun sample=>σ • disorderVectorBrownianIncrement r t sample) V sample)
      (vectorDisorderBrownianMeasure n) ∧
    |∫ sample,Z sample*vectorSpatialTaylorError f X
      (fun sample=>σ • disorderVectorBrownianIncrement r t sample) V sample
      ∂vectorDisorderBrownianMeasure n| ≤
      C*(2*K₃*|σ|^3*vectorGaussianNormMoment n 3*((t : ℝ)-r)*Real.sqrt ((t : ℝ)-r)+
        2*K₃*(D*((t : ℝ)-r))^3+
        K₂*|σ| *(D*((t : ℝ)-r))*Real.sqrt ((t : ℝ)-r)*vectorGaussianNormMoment n 1+
        K₂/2*(D*((t : ℝ)-r))^2) := by
  let Δ : ℝ := (t : ℝ)-r
  let M : ℝ := D*Δ
  let A : ℝ := 2*K₃*|σ|^3
  let B : ℝ := 2*K₃*M^3
  let L : ℝ := K₂*|σ| *M
  let J : ℝ := K₂/2*M^2
  let H : VectorDisorderBrownianSample n → ℝ := fun sample=>
    C*(A*‖disorderVectorBrownianIncrement r t sample‖^3+B+
      L*‖disorderVectorBrownianIncrement r t sample‖+J)
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrt)
  have hM : 0 ≤ M := mul_nonneg D.coe_nonneg hΔ
  have h1 : Integrable (fun sample=>‖disorderVectorBrownianIncrement (n := n) r t sample‖)
      (vectorDisorderBrownianMeasure n) := by
    simpa only [pow_one] using integrable_disorderVectorBrownianIncrement_norm_pow (n := n) r t hrt 1
  have h3 := integrable_disorderVectorBrownianIncrement_norm_pow (n := n) r t hrt 3
  have hAB := (h3.const_mul A).add (integrable_const B)
  have hABL := hAB.add (h1.const_mul L)
  have hALL := hABL.add (integrable_const J)
  have hH : Integrable H (vectorDisorderBrownianMeasure n) := by
    simpa only [H,Pi.add_apply] using hALL.const_mul (C : ℝ)
  have hb (sample : VectorDisorderBrownianSample n) :
      ‖Z sample*vectorSpatialTaylorError f X
        (fun sample=>σ • disorderVectorBrownianIncrement r t sample) V sample‖ ≤ H sample := by
    have ht := vector_bounded_drift_taylor_bound (hf sample) K₂.coe_nonneg K₃.coe_nonneg hM
      (h₂ sample) (h₃ sample) (X sample)
      (σ • disorderVectorBrownianIncrement r t sample) (V sample) (hV sample)
    simp only [norm_smul,Real.norm_eq_abs,mul_pow] at ht
    rw [norm_mul,Real.norm_eq_abs]
    change ‖Z sample‖*|f sample (X sample+σ • disorderVectorBrownianIncrement r t sample+V sample)-
      vectorNoiseDriftTaylorPolynomial (f sample) (X sample)
        (σ • disorderVectorBrownianIncrement r t sample) (V sample)| ≤ _
    have hh := mul_le_mul (hC sample) ht (abs_nonneg _) C.coe_nonneg
    convert hh using 1 <;> dsimp only [H,A,B,L,J] <;> ring
  have hInt : Integrable (fun sample=>Z sample*vectorSpatialTaylorError f X
      (fun sample=>σ • disorderVectorBrownianIncrement r t sample) V sample)
      (vectorDisorderBrownianMeasure n) := hH.mono' hR (.of_forall hb)
  have hHval : (∫ sample,H sample ∂vectorDisorderBrownianMeasure n) =
      C*(A*(vectorGaussianNormMoment n 3*Δ*Real.sqrt Δ)+B+
        L*(Real.sqrt Δ*vectorGaussianNormMoment n 1)+J) := by
    dsimp only [H]
    rw [integral_const_mul]
    have hsum := integral_add hABL (integrable_const J)
    have hsum' := integral_add hAB (h1.const_mul L)
    have hsum'' := integral_add (h3.const_mul A) (integrable_const B)
    simp only [Pi.add_apply] at hsum hsum' hsum''
    rw [hsum,hsum',hsum'']
    rw [integral_const_mul A,integral_const_mul L,
      integral_disorderVectorBrownianIncrement_norm_cube r t hrt]
    have hone := integral_disorderVectorBrownianIncrement_norm_pow (n := n) r t hrt 1
    simp only [pow_one] at hone
    rw [hone]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    rfl
  refine ⟨hInt,?_⟩
  calc
    _ ≤ ∫ sample,‖Z sample*vectorSpatialTaylorError f X
        (fun sample=>σ • disorderVectorBrownianIncrement r t sample) V sample‖
        ∂vectorDisorderBrownianMeasure n := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun sample=>Z sample*vectorSpatialTaylorError f X
          (fun sample=>σ • disorderVectorBrownianIncrement r t sample) V sample)
    _ ≤ ∫ sample,H sample ∂vectorDisorderBrownianMeasure n :=
      integral_mono hInt.norm hH hb
    _ = _ := by rw [hHval]; dsimp only [A,B,L,J,M,Δ];ring

end QuantitativePaper
