module
public import FourPapersCommon.FiniteCascadeTreeFeatureDifferentiation

@[expose] public section

/-! Actual normalized tree response to a terminal feature. Both the
numerator and the genuine Gaussian one-leaf normalizer are differentiated
under their fixed reference measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem hasDerivAt_finiteCascadeTreeGaussianFeatureNormalizer
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C) :
    HasDerivAt (fun u=>finiteCascadeTreeGaussianNormalizer (fun σ=>V σ+u*K σ) a L s j R H)
      (∫z,Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)*
        finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ
        ∂finiteCascadeTreeGaussianReferenceLaw L T R H) θ := by
  have he : (fun u=>finiteCascadeTreeGaussianNormalizer (fun σ=>V σ+u*K σ) a L s j R H)=
      fun u=>∫z,Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 u)
        ∂finiteCascadeTreeGaussianReferenceLaw L T R H := by
    funext u
    exact (integral_exp_finiteCascadeTreeFeatureLogNumerator V K a ha L s u T R H).symm
  rw [he]
  simpa only [one_mul] using hasDerivAt_integral_finiteCascadeTreeFeatureNumerator
    V K a ha hanti h0 L s θ T hs R H C hC hK (fun _=>1) measurable_const 1
      (by norm_num) (fun _=>by norm_num)

theorem hasDerivAt_finiteCascadeTreeGaussianFeatureExpectation
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    HasDerivAt (fun u=>∫z,F z ∂finiteCascadeTreeGaussianFeatureLaw V K a L s u T R H)
      ((∫z,F z*finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ
          ∂finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H)-
        (∫z,F z ∂finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H)*
          (∫z,finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ
            ∂finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H)) θ := by
  have hn := hasDerivAt_integral_finiteCascadeTreeFeatureNumerator
    V K a ha hanti h0 L s θ T hs R H C hC hK F hF CF hCF hFb
  have hz := hasDerivAt_finiteCascadeTreeGaussianFeatureNormalizer
    V K a ha hanti h0 L s θ T hs R H C hC hK
  have hpos := finiteCascadeTreeGaussianNormalizer_pos (fun σ=>V σ+θ*K σ) a ha L s j R H
  have hd := hn.div hz hpos.ne'
  have he : (fun u=>∫z,F z ∂finiteCascadeTreeGaussianFeatureLaw V K a L s u T R H)=
      fun u=>(∫z,F z*Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 u)
        ∂finiteCascadeTreeGaussianReferenceLaw L T R H)/
          finiteCascadeTreeGaussianNormalizer (fun σ=>V σ+u*K σ) a L s j R H := by
    funext u
    exact integral_finiteCascadeTreeGaussianFeatureLaw_eq V K a ha L s u T R H F
  rw [he]
  apply hd.congr_deriv
  rw [integral_finiteCascadeTreeGaussianFeatureLaw_eq V K a ha L s θ T R H,
    integral_finiteCascadeTreeGaussianFeatureLaw_eq V K a ha L s θ T R H F,
    integral_finiteCascadeTreeGaussianFeatureLaw_eq V K a ha L s θ T R H]
  have hi : (∫z,(F z*finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ)*
      Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)
      ∂finiteCascadeTreeGaussianReferenceLaw L T R H)=
    ∫z,F z*Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)*
      finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ
      ∂finiteCascadeTreeGaussianReferenceLaw L T R H := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z=>by ring
  rw [hi]
  have hj : (∫z,finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ*
      Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)
      ∂finiteCascadeTreeGaussianReferenceLaw L T R H)=
    ∫z,Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)*
      finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ
      ∂finiteCascadeTreeGaussianReferenceLaw L T R H := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z=>mul_comm _ _
  rw [hj]
  field_simp
  <;> ring

end FourPapersCommon
