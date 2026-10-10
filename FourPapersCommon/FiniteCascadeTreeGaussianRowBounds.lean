module
public import FourPapersCommon.FiniteCascadeTreeGaussianRowResponse
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Dimension-independent bounds and closed-variance regularity of the
actual normalized Gaussian-row expectation. These estimates retain the
normalizer response and the one-sided zero-variance derivative. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy FRSB
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

def finiteCascadeTreeGaussianRowVarianceResponse
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s v : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ) : ℝ :=
  (1/2:ℝ)*((∫z,F z.2*finiteCascadeTreeGaussianRowCurvature V K a L s T z
    ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H)-
      (∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H)*
        (∫z,finiteCascadeTreeGaussianRowCurvature V K a L s T z
          ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H))

theorem finiteCascadeTreeGaussianRowVarianceResponse_abs_le
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s v : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    |finiteCascadeTreeGaussianRowVarianceResponse V K a L s v T R H F|≤
      CF*(|(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|^2+
        |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2|) := by
  let P:=finiteCascadeTreeGaussianRowLaw V K a L s v T R H
  let A:=|(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|^2+
    |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2|
  let Q:=finiteCascadeTreeGaussianRowCurvature V K a L s T
  letI:=finiteCascadeTreeGaussianRowLaw_probability V K a ha hanti h0 L s v T hs R H C hC hK
  have hQ (z) : |Q z|≤A:=finiteCascadeTreeGaussianRowCurvature_abs_le
    V K a ha hanti h0 L s T hs C hC hK z
  have hEF : |∫z,F z.2∂P|≤CF := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=P) (f:=fun z=>F z.2)
        (.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hFb z.2)
  have hEQ : |∫z,Q z∂P|≤A := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=P) (f:=Q)
        (.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hQ z)
  have hEFQ : |∫z,F z.2*Q z∂P|≤CF*A := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=P) (f:=fun z=>F z.2*Q z)
        (.of_forall fun z=>by
          rw [Real.norm_eq_abs,abs_mul]
          exact mul_le_mul (hFb z.2) (hQ z) (abs_nonneg _) hCF)
  change |(1/2:ℝ)*((∫z,F z.2*Q z∂P)-(∫z,F z.2∂P)*(∫z,Q z∂P))|≤CF*A
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  have hprod : |(∫z,F z.2∂P)*(∫z,Q z∂P)|≤CF*A := by
    rw [abs_mul]
    exact mul_le_mul hEF hEQ (abs_nonneg _) hCF
  have hd:=abs_sub (∫z,F z.2*Q z∂P) ((∫z,F z.2∂P)*(∫z,Q z∂P))
  linarith

theorem continuous_finiteCascadeTreeGaussianRowExpectation_variance
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    Continuous (fun v=>∫z,F z.2∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H) := by
  have hNF:=heatC2Datum_finiteCascadeTreeFeatureNumerator
    V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb
  have hN1:=heatC2Datum_finiteCascadeTreeFeatureNumerator
    V K a ha hanti h0 L s T hs R H C hC hK (fun _=>1) measurable_const 1
      (by norm_num) (fun _=>by norm_num)
  simp_rw [integral_finiteCascadeTreeGaussianRowLaw_eq
    V K a ha hanti h0 L s _ T hs R H C hC hK F hF CF hCF hFb]
  exact ((continuous_gaussianHeatFlow hNF).comp
      (continuous_id.prodMk continuous_const)).div
    ((continuous_gaussianHeatFlow hN1).comp (continuous_id.prodMk continuous_const))
    (fun v=>(finiteCascadeTreeGaussianRowNormalizer_pos
      V K a ha hanti h0 L s v T hs R H C hC hK).ne')

theorem lipschitzOnWith_finiteCascadeTreeGaussianRowExpectation_variance
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    LipschitzOnWith (CF*(|(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|^2+
      |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2|)).toNNReal
      (fun v=>∫z,F z.2∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H) (Ici (0:ℝ)) := by
  apply (convex_Ici (0:ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f':=fun v=>finiteCascadeTreeGaussianRowVarianceResponse V K a L s v T R H F)
  · intro v hv
    change (0:ℝ)≤v at hv
    rcases hv.eq_or_lt with hzero|hpos
    · subst v
      exact hasDerivWithinAt_finiteCascadeTreeGaussianRowExpectation_variance_zero
        V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb
    · exact (hasDerivAt_finiteCascadeTreeGaussianRowExpectation_variance
        V K a ha hanti h0 L s v hpos T hs R H C hC hK F hF CF hCF hFb).hasDerivWithinAt
  · intro v hv
    rw [←NNReal.coe_le_coe,coe_nnnorm,Real.norm_eq_abs,Real.coe_toNNReal _ (by positivity)]
    exact finiteCascadeTreeGaussianRowVarianceResponse_abs_le
      V K a ha hanti h0 L s v T hs R H C hC hK F CF hCF hFb

end FourPapersCommon
