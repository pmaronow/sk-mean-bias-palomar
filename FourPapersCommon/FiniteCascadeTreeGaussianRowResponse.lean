module
public import FourPapersCommon.FiniteCascadeTreeGaussianRowMoments

@[expose] public section

/-! Genuine Gaussian row-variance differentiation under the normalized
recorded tree law, including the one-sided zero-variance response. The
heat data and both normalizer derivatives are actual cascade integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy FRSB
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem iteratedDeriv_two_finiteCascadeTreeFeatureNumerator
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    iteratedDeriv 2 (finiteCascadeTreeFeatureNumerator V K a L s T R H F)=
      finiteCascadeTreeFeatureNumeratorSecond V K a L s T R H F := by
  have he : deriv (finiteCascadeTreeFeatureNumerator V K a L s T R H F)=
      finiteCascadeTreeFeatureNumeratorFirst V K a L s T R H F := by
    funext θ
    exact (hasDerivAt_integral_finiteCascadeTreeFeatureNumerator
      V K a ha hanti h0 L s θ T hs R H C hC hK F hF CF hCF hFb).deriv
  have he₁ : deriv (finiteCascadeTreeFeatureNumeratorFirst V K a L s T R H F)=
      finiteCascadeTreeFeatureNumeratorSecond V K a L s T R H F := by
    funext θ
    exact (hasDerivAt_integral_finiteCascadeTreeFeatureNumerator_derivative
      V K a ha hanti h0 L s θ T hs R H C hC hK F hF CF hCF hFb).deriv
  rw [iteratedDeriv_succ,iteratedDeriv_one,he,he₁]

theorem hasDerivAt_finiteCascadeTreeGaussianRowExpectation_variance
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s v : ℝ) (hv : 0<v)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    HasDerivAt (fun u=>∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s u T R H)
      ((1/2:ℝ)*((∫z,F z.2*finiteCascadeTreeGaussianRowCurvature V K a L s T z
        ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H)-
        (∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H)*
          (∫z,finiteCascadeTreeGaussianRowCurvature V K a L s T z
            ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H))) v := by
  have hNF := heatC2Datum_finiteCascadeTreeFeatureNumerator
    V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb
  have hN1 := heatC2Datum_finiteCascadeTreeFeatureNumerator
    V K a ha hanti h0 L s T hs R H C hC hK (fun _=>1) measurable_const 1
      (by norm_num) (fun _=>by norm_num)
  have hdF := hasDerivAt_gaussianHeatFlow_variance hNF hv 0
  have hd1 := hasDerivAt_gaussianHeatFlow_variance hN1 hv 0
  rw [iteratedDeriv_two_finiteCascadeTreeFeatureNumerator
    V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb] at hdF
  rw [iteratedDeriv_two_finiteCascadeTreeFeatureNumerator
    V K a ha hanti h0 L s T hs R H C hC hK (fun _=>1) measurable_const 1
      (by norm_num) (fun _=>by norm_num)] at hd1
  have hp := finiteCascadeTreeGaussianRowNormalizer_pos
    V K a ha hanti h0 L s v T hs R H C hC hK
  have he : (fun u=>∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s u T R H)=
      fun u=>gaussianHeatFlow (finiteCascadeTreeFeatureNumerator V K a L s T R H F) u 0/
        finiteCascadeTreeGaussianRowNormalizer V K a L s u T R H := by
    funext u
    exact integral_finiteCascadeTreeGaussianRowLaw_eq
      V K a ha hanti h0 L s u T hs R H C hC hK F hF CF hCF hFb
  rw [he]
  apply (hdF.div hd1 hp.ne').congr_deriv
  rw [integral_finiteCascadeTreeGaussianRowCurvature_mul_eq
    V K a ha hanti h0 L s v T hs R H C hC hK F hF CF hCF hFb,
    integral_finiteCascadeTreeGaussianRowLaw_eq
      V K a ha hanti h0 L s v T hs R H C hC hK F hF CF hCF hFb]
  have hc := integral_finiteCascadeTreeGaussianRowCurvature_mul_eq
    V K a ha hanti h0 L s v T hs R H C hC hK (fun _=>1) measurable_const 1
      (by norm_num) (fun _=>by norm_num)
  simp only [one_mul] at hc
  rw [hc]
  dsimp only [finiteCascadeTreeGaussianRowNormalizer]
  field_simp
  <;> ring

theorem hasDerivWithinAt_finiteCascadeTreeGaussianRowExpectation_variance_zero
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    HasDerivWithinAt (fun u=>∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s u T R H)
      ((1/2:ℝ)*((∫z,F z.2*finiteCascadeTreeGaussianRowCurvature V K a L s T z
        ∂finiteCascadeTreeGaussianRowLaw V K a L s 0 T R H)-
        (∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s 0 T R H)*
          (∫z,finiteCascadeTreeGaussianRowCurvature V K a L s T z
            ∂finiteCascadeTreeGaussianRowLaw V K a L s 0 T R H))) (Ici (0:ℝ)) 0 := by
  have hNF := heatC2Datum_finiteCascadeTreeFeatureNumerator
    V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb
  have hN1 := heatC2Datum_finiteCascadeTreeFeatureNumerator
    V K a ha hanti h0 L s T hs R H C hC hK (fun _=>1) measurable_const 1
      (by norm_num) (fun _=>by norm_num)
  have hdF := hasDerivWithinAt_gaussianHeatFlow_variance_zero hNF 0
  have hd1 := hasDerivWithinAt_gaussianHeatFlow_variance_zero hN1 0
  rw [iteratedDeriv_two_finiteCascadeTreeFeatureNumerator
    V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb] at hdF
  rw [iteratedDeriv_two_finiteCascadeTreeFeatureNumerator
    V K a ha hanti h0 L s T hs R H C hC hK (fun _=>1) measurable_const 1
      (by norm_num) (fun _=>by norm_num)] at hd1
  have hp := finiteCascadeTreeGaussianRowNormalizer_pos
    V K a ha hanti h0 L s 0 T hs R H C hC hK
  have he : (fun u=>∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s u T R H)=
      fun u=>gaussianHeatFlow (finiteCascadeTreeFeatureNumerator V K a L s T R H F) u 0/
        finiteCascadeTreeGaussianRowNormalizer V K a L s u T R H := by
    funext u
    exact integral_finiteCascadeTreeGaussianRowLaw_eq
      V K a ha hanti h0 L s u T hs R H C hC hK F hF CF hCF hFb
  rw [he]
  apply (hdF.div hd1 hp.ne').congr_deriv
  rw [integral_finiteCascadeTreeGaussianRowCurvature_mul_eq
    V K a ha hanti h0 L s 0 T hs R H C hC hK F hF CF hCF hFb,
    integral_finiteCascadeTreeGaussianRowLaw_eq
      V K a ha hanti h0 L s 0 T hs R H C hC hK F hF CF hCF hFb]
  have hc := integral_finiteCascadeTreeGaussianRowCurvature_mul_eq
    V K a ha hanti h0 L s 0 T hs R H C hC hK (fun _=>1) measurable_const 1
      (by norm_num) (fun _=>by norm_num)
  simp only [one_mul] at hc
  rw [hc]
  dsimp only [finiteCascadeTreeGaussianRowNormalizer]
  simp only [gaussianHeatFlow_zero]
  field_simp
  <;> ring

end FourPapersCommon
