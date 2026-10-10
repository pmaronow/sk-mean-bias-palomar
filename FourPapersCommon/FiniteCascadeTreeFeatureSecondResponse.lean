module
public import FourPapersCommon.FiniteCascadeTreeFeatureResponse
public import FourPapersCommon.FiniteCascadeTreeFeatureSecondDifferentiation

@[expose] public section

/-! Genuine second normalized terminal-feature response. The two numerator
and normalizer derivatives are obtained from the actual tree density, with
no integral-response hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

private theorem hasDerivAt_deriv_ratio
    (f f₁ f₂ g g₁ g₂ : ℝ→ℝ) (θ : ℝ)
    (hf : ∀u,HasDerivAt f (f₁ u) u) (hg : ∀u,HasDerivAt g (g₁ u) u)
    (hf₁ : HasDerivAt f₁ (f₂ θ) θ) (hg₁ : HasDerivAt g₁ (g₂ θ) θ)
    (hgn : ∀u,g u≠0) :
    HasDerivAt (fun u=>deriv (fun v=>f v/g v) u)
      (f₂ θ/g θ-f θ*g₂ θ/(g θ)^2-
        2*(f₁ θ/g θ)*(g₁ θ/g θ)+2*(f θ/g θ)*(g₁ θ/g θ)^2) θ := by
  have he : (fun u=>deriv (fun v=>f v/g v) u)=
      fun u=>(f₁ u*g u-f u*g₁ u)/(g u)^2 := by
    funext u
    exact ((hf u).div (hg u) (hgn u)).deriv
  rw [he]
  apply ((((hf₁.mul (hg θ)).sub ((hf θ).mul hg₁)).div
    ((hg θ).pow 2) (pow_ne_zero 2 (hgn θ))).congr_deriv)
  simp only [Pi.pow_apply,Pi.mul_apply,Pi.sub_apply]
  field_simp [hgn θ]
  <;> ring

theorem hasDerivAt_finiteCascadeTreeGaussianFeatureNormalizer_derivative
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C) :
    HasDerivAt (fun u=>deriv (fun v=>finiteCascadeTreeGaussianNormalizer
      (fun σ=>V σ+v*K σ) a L s j R H) u)
      (∫z,Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)*
        ((finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ)^2-
          finiteCascadeTreeFeatureSecondCharge V a L s T z.1 K z.2 θ)
        ∂finiteCascadeTreeGaussianReferenceLaw L T R H) θ := by
  have he : (fun u=>deriv (fun v=>finiteCascadeTreeGaussianNormalizer
      (fun σ=>V σ+v*K σ) a L s j R H) u)=
      fun u=>∫z,Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 u)*
        finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 u
        ∂finiteCascadeTreeGaussianReferenceLaw L T R H := by
    funext u
    exact (hasDerivAt_finiteCascadeTreeGaussianFeatureNormalizer
      V K a ha hanti h0 L s u T hs R H C hC hK).deriv
  rw [he]
  simpa only [one_mul] using hasDerivAt_integral_finiteCascadeTreeFeatureNumerator_derivative
    V K a ha hanti h0 L s θ T hs R H C hC hK (fun _=>1) measurable_const 1
      (by norm_num) (fun _=>by norm_num)

theorem hasDerivAt_finiteCascadeTreeGaussianFeatureExpectation_derivative
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    HasDerivAt (fun u=>deriv (fun v=>∫z,F z
      ∂finiteCascadeTreeGaussianFeatureLaw V K a L s v T R H) u)
      ((∫z,F z*((finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ)^2-
          finiteCascadeTreeFeatureSecondCharge V a L s T z.1 K z.2 θ)
          ∂finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H)-
        (∫z,F z ∂finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H)*
          (∫z,(finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ)^2-
            finiteCascadeTreeFeatureSecondCharge V a L s T z.1 K z.2 θ
            ∂finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H)-
        2*(∫z,F z*finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ
          ∂finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H)*
          (∫z,finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ
            ∂finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H)+
        2*(∫z,F z ∂finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H)*
          (∫z,finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ
            ∂finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H)^2) θ := by
  let P := finiteCascadeTreeGaussianReferenceLaw L T R H
  let N := fun u (z : FiniteStateField S×Records (FiniteStateField S) S T)=>finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 u
  let Q := fun u (z : FiniteStateField S×Records (FiniteStateField S) S T)=>finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 u
  let E := fun u (z : FiniteStateField S×Records (FiniteStateField S) S T)=>finiteCascadeTreeFeatureSecondCharge V a L s T z.1 K z.2 u
  let f := fun u=>∫z,F z*Real.exp (N u z) ∂P
  let f₁ := fun u=>∫z,F z*Real.exp (N u z)*Q u z ∂P
  let f₂ := fun u=>∫z,F z*Real.exp (N u z)*((Q u z)^2-E u z) ∂P
  let g := fun u=>finiteCascadeTreeGaussianNormalizer (fun σ=>V σ+u*K σ) a L s j R H
  let g₁ := fun u=>∫z,Real.exp (N u z)*Q u z ∂P
  let g₂ := fun u=>∫z,Real.exp (N u z)*((Q u z)^2-E u z) ∂P
  have hf : ∀u,HasDerivAt f (f₁ u) u := fun u=>
    hasDerivAt_integral_finiteCascadeTreeFeatureNumerator
      V K a ha hanti h0 L s u T hs R H C hC hK F hF CF hCF hFb
  have hg : ∀u,HasDerivAt g (g₁ u) u := fun u=>
    hasDerivAt_finiteCascadeTreeGaussianFeatureNormalizer
      V K a ha hanti h0 L s u T hs R H C hC hK
  have hf₁ : HasDerivAt f₁ (f₂ θ) θ :=
    hasDerivAt_integral_finiteCascadeTreeFeatureNumerator_derivative
      V K a ha hanti h0 L s θ T hs R H C hC hK F hF CF hCF hFb
  have hg₁ : HasDerivAt g₁ (g₂ θ) θ := by
    simpa only [one_mul] using hasDerivAt_integral_finiteCascadeTreeFeatureNumerator_derivative
      V K a ha hanti h0 L s θ T hs R H C hC hK (fun _=>1) measurable_const 1
        (by norm_num) (fun _=>by norm_num)
  have hgn : ∀u,g u≠0 := fun u=>(finiteCascadeTreeGaussianNormalizer_pos
    (fun σ=>V σ+u*K σ) a ha L s j R H).ne'
  have he : (fun u=>∫z,F z ∂finiteCascadeTreeGaussianFeatureLaw V K a L s u T R H)=
      fun u=>f u/g u := by
    funext u
    exact integral_finiteCascadeTreeGaussianFeatureLaw_eq V K a ha L s u T R H F
  rw [he]
  apply (hasDerivAt_deriv_ratio f f₁ f₂ g g₁ g₂ θ hf hg hf₁ hg₁ hgn).congr_deriv
  simp only [integral_finiteCascadeTreeGaussianFeatureLaw_eq V K a ha L s θ T R H]
  have hi (G : FiniteStateField S×Records (FiniteStateField S) S T→ℝ) :
      (∫z,(F z*G z)*Real.exp (N θ z) ∂P)=
        ∫z,F z*Real.exp (N θ z)*G z ∂P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z=>by ring
  have hj (G : FiniteStateField S×Records (FiniteStateField S) S T→ℝ) :
      (∫z,G z*Real.exp (N θ z) ∂P)=∫z,Real.exp (N θ z)*G z ∂P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z=>mul_comm _ _
  change f₂ θ/g θ-f θ*g₂ θ/(g θ)^2-2*(f₁ θ/g θ)*(g₁ θ/g θ)+
    2*(f θ/g θ)*(g₁ θ/g θ)^2 = _
  change _ = (∫z,(F z*((Q θ z)^2-E θ z))*Real.exp (N θ z) ∂P)/g θ-
    (f θ/g θ)*((∫z,((Q θ z)^2-E θ z)*Real.exp (N θ z) ∂P)/g θ)-
    2*((∫z,(F z*Q θ z)*Real.exp (N θ z) ∂P)/g θ)*
      ((∫z,Q θ z*Real.exp (N θ z) ∂P)/g θ)+
    2*(f θ/g θ)*((∫z,Q θ z*Real.exp (N θ z) ∂P)/g θ)^2
  rw [hi,hj,hi,hj]
  dsimp only [f₂,g₂,f₁,g₁]
  field_simp [hgn θ]
  <;> ring

end FourPapersCommon
