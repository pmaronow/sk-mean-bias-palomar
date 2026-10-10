module
public import FourPapersCommon.FiniteCascadeTreeFeatureLaw

@[expose] public section

/-! Integral normalization of the genuine finite feature-perturbed tree
law. Its numerator is integrable against the fixed Gaussian reference
measure and integrates to the actual one-leaf normalizer. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem integrable_exp_finiteCascadeTreeFeatureLogNumerator (V : S→ℝ) (K : FiniteStateField S)
    (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    Integrable (fun z=>Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ))
      (finiteCascadeTreeGaussianReferenceLaw L T R H) := by
  let Z := finiteCascadeTreeGaussianNormalizer (fun σ=>V σ+θ*K σ) a L s j R H
  have hZ : 0<Z := finiteCascadeTreeGaussianNormalizer_pos _ _ ha _ _ _ _ _
  haveI := finiteCascadeTreeGaussianFeatureLaw_probability V K a ha L s θ T R H
  have hi : Integrable (fun _ : FiniteStateField S×Records (FiniteStateField S) S T=>(1:ℝ))
      (finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H) := integrable_const 1
  rw [finiteCascadeTreeGaussianFeatureLaw_density V K a ha L s θ T R H] at hi
  have hm := ((measurable_finiteCascadeTreeFeatureLogNumerator V K a ha L s θ T).exp.div_const Z).ennreal_ofReal
  have hid := (integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall fun _=>ENNReal.ofReal_lt_top)).mp hi
  simp only [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ.le),
    smul_eq_mul,mul_one] at hid
  convert hid.mul_const Z using 1
  funext z
  exact (div_mul_cancel₀ _ hZ.ne').symm

theorem integral_exp_finiteCascadeTreeFeatureLogNumerator (V : S→ℝ) (K : FiniteStateField S)
    (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    (∫z,Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)
      ∂finiteCascadeTreeGaussianReferenceLaw L T R H)=
        finiteCascadeTreeGaussianNormalizer (fun σ=>V σ+θ*K σ) a L s j R H := by
  let Z := finiteCascadeTreeGaussianNormalizer (fun σ=>V σ+θ*K σ) a L s j R H
  have hZ : 0<Z := finiteCascadeTreeGaussianNormalizer_pos _ _ ha _ _ _ _ _
  haveI := finiteCascadeTreeGaussianFeatureLaw_probability V K a ha L s θ T R H
  have he : (∫_ : FiniteStateField S×Records (FiniteStateField S) S T,(1:ℝ)
      ∂finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H)=1 := by simp
  rw [finiteCascadeTreeGaussianFeatureLaw_density V K a ha L s θ T R H] at he
  have hm := ((measurable_finiteCascadeTreeFeatureLogNumerator V K a ha L s θ T).exp.div_const Z).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall fun _=>ENNReal.ofReal_lt_top)] at he
  simp only [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ.le),
    smul_eq_mul,mul_one] at he
  rw [integral_div] at he
  exact (div_eq_one_iff_eq hZ.ne').mp he

theorem integral_finiteCascadeTreeGaussianFeatureLaw_eq (V : S→ℝ) (K : FiniteStateField S)
    (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ) :
    (∫z,F z ∂finiteCascadeTreeGaussianFeatureLaw V K a L s θ T R H)=
      (∫z,F z*Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)
        ∂finiteCascadeTreeGaussianReferenceLaw L T R H)/
          finiteCascadeTreeGaussianNormalizer (fun σ=>V σ+θ*K σ) a L s j R H := by
  let Z := finiteCascadeTreeGaussianNormalizer (fun σ=>V σ+θ*K σ) a L s j R H
  have hZ : 0<Z := finiteCascadeTreeGaussianNormalizer_pos _ _ ha _ _ _ _ _
  rw [finiteCascadeTreeGaussianFeatureLaw_density V K a ha L s θ T R H]
  have hm := ((measurable_finiteCascadeTreeFeatureLogNumerator V K a ha L s θ T).exp.div_const Z).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall fun _=>ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ.le),smul_eq_mul]
  rw [←integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z=>by ring

end FourPapersCommon
