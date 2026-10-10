module
public import FourPapersCommon.FiniteCascadeTreeGaussianRowLaw

@[expose] public section

/-! The actual Gaussian-row curvature observable and its normalized
moment. Both score-square and second vertex charge are evaluated on the
same recorded tree, under its genuine normalized joint law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy FRSB
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

def finiteCascadeTreeGaussianRowCurvature (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (z : ℝ×(FiniteStateField S×Records (FiniteStateField S) S T)) : ℝ :=
  (finiteCascadeTreeFeatureScore V a L s T z.2.1 K z.2.2 z.1)^2-
    finiteCascadeTreeFeatureSecondCharge V a L s T z.2.1 K z.2.2 z.1

theorem measurable_finiteCascadeTreeGaussianRowCurvature
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (finiteCascadeTreeGaussianRowCurvature V K a L s T) := by
  have hq : Measurable (fun z : ℝ×(FiniteStateField S×Records (FiniteStateField S) S T)=>
      finiteCascadeTreeFeatureScore V a L s T z.2.1 K z.2.2 z.1) := by
    apply measurable_uncurry_of_continuous_of_measurable
      (u:=fun θ (z : FiniteStateField S×Records (FiniteStateField S) S T)=>
        finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ)
    · intro z
      exact continuous_iff_continuousAt.mpr fun θ=>
        (hasDerivAt_finiteCascadeTreeFeatureScore V a ha L s T z.1 K z.2 θ).continuousAt
    · intro θ
      exact measurable_finiteCascadeTreeFeatureScore V K a ha L s θ T
  have he : Measurable (fun z : ℝ×(FiniteStateField S×Records (FiniteStateField S) S T)=>
      finiteCascadeTreeFeatureSecondCharge V a L s T z.2.1 K z.2.2 z.1) := by
    apply measurable_uncurry_of_continuous_of_measurable
      (u:=fun θ (z : FiniteStateField S×Records (FiniteStateField S) S T)=>
        finiteCascadeTreeFeatureSecondCharge V a L s T z.1 K z.2 θ)
    · intro z
      exact continuous_finiteCascadeTreeFeatureSecondCharge V a ha L s T z.1 K z.2
    · intro θ
      exact measurable_finiteCascadeTreeFeatureSecondCharge V K a ha L s θ T
  exact (hq.pow_const 2).sub he

theorem finiteCascadeTreeGaussianRowCurvature_abs_le
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (z : ℝ×(FiniteStateField S×Records (FiniteStateField S) S T)) :
    |finiteCascadeTreeGaussianRowCurvature V K a L s T z|≤
      |(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|^2+
        |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2| := by
  apply (abs_sub _ _).trans
  apply add_le_add
  · rw [abs_sq]
    have hq : |finiteCascadeTreeFeatureScore V a L s T z.2.1 K z.2.2 z.1|≤
        |(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C| :=
      (finiteCascadeTreeFeatureScore_abs_le_of_pointwise
        V a ha hanti h0 L s T hs z.2.1 K C hC hK z.2.2 z.1).trans (le_abs_self _)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hq 2
  · exact (finiteCascadeTreeFeatureSecondCharge_abs_le_of_pointwise
      V a ha hanti h0 L s T hs z.2.1 K C hC hK z.2.2 z.1).trans (le_abs_self _)

theorem integral_finiteCascadeTreeGaussianRowLaw_bounded_eq
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s v : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : ℝ×(FiniteStateField S×Records (FiniteStateField S) S T)→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    (∫z,F z ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H)=
      (∫θ,∫z,F (θ,z)*Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)
        ∂finiteCascadeTreeGaussianReferenceLaw L T R H ∂gaussianReal 0 v.toNNReal)/
        finiteCascadeTreeGaussianRowNormalizer V K a L s v T R H := by
  have hi := integrable_exp_finiteCascadeTreeGaussianRowLogNumerator
    V K a ha hanti h0 L s v T hs R H C hC hK
  have hIF : Integrable (fun z=>Real.exp (finiteCascadeTreeGaussianRowLogNumerator V K a L s T z)*F z)
      (finiteCascadeTreeGaussianRowReference L v T R H) :=
    (hi.mul_const CF).mono'
      (((measurable_finiteCascadeTreeGaussianRowLogNumerator V K a ha L s T).exp.mul hF).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z=>by
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hFb z) (Real.exp_pos _).le)
  unfold finiteCascadeTreeGaussianRowLaw
  rw [integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div]
  rw [integral_div,integral_exp_finiteCascadeTreeGaussianRowLogNumerator
    V K a ha hanti h0 L s v T hs R H C hC hK,finiteCascadeTreeGaussianRowReference,integral_prod _ hIF]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ=>integral_congr_ae
    (Filter.Eventually.of_forall fun z=>mul_comm _ _)

theorem integral_finiteCascadeTreeGaussianRowCurvature_mul_eq
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s v : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    (∫z,F z.2*finiteCascadeTreeGaussianRowCurvature V K a L s T z
      ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H)=
      gaussianHeatFlow (finiteCascadeTreeFeatureNumeratorSecond V K a L s T R H F) v 0/
        finiteCascadeTreeGaussianRowNormalizer V K a L s v T R H := by
  let A := |(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|^2+
    |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2|
  have he := integral_finiteCascadeTreeGaussianRowLaw_bounded_eq
    V K a ha hanti h0 L s v T hs R H C hC hK
    (fun z=>F z.2*finiteCascadeTreeGaussianRowCurvature V K a L s T z)
    ((hF.comp measurable_snd).mul (measurable_finiteCascadeTreeGaussianRowCurvature V K a ha L s T))
    (CF*A) (by positivity) (fun z=>by
      rw [abs_mul]
      exact mul_le_mul (hFb z.2)
        (finiteCascadeTreeGaussianRowCurvature_abs_le V K a ha hanti h0 L s T hs C hC hK z)
        (abs_nonneg _) hCF)
  rw [he]
  congr 1
  simp only [gaussianHeatFlow,finiteCascadeTreeFeatureNumeratorSecond,zero_add]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ=>integral_congr_ae
    (Filter.Eventually.of_forall fun z=>by unfold finiteCascadeTreeGaussianRowCurvature;ring)

end FourPapersCommon
