module
public import FourPapersCommon.FiniteCascadeTreeFeatureHeatData

@[expose] public section

/-! Actual exponential-growth heat data for a finite Gaussian tree
numerator. The common integrable coefficient is its genuine normalizer at
zero feature, while the rate follows from the bounded terminal feature. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem finiteCascadeTreeFeature_factor_integral_growth
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F G : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (CF A : ℝ) (hCF : 0≤CF) (hA : 0≤A) (hFb : ∀z,|F z|≤CF) (hGb : ∀z,|G z|≤A) :
    |∫z,F z*Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)*G z
      ∂finiteCascadeTreeGaussianReferenceLaw L T R H| ≤
      CF*A*finiteCascadeTreeGaussianNormalizer V a L s j R H*
        Real.exp (|(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C| * |θ|) := by
  let B := |(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|
  let N := fun u (z : FiniteStateField S×Records (FiniteStateField S) S T)=>
    finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 u
  have hB : 0≤B := abs_nonneg _
  have hExp (z : FiniteStateField S×Records (FiniteStateField S) S T) :
      Real.exp (N θ z)≤Real.exp (N 0 z)*Real.exp (B*|θ|) := by
    have hl := finiteCascadeTreeFeatureLogNumerator_lipschitz_of_pointwise
      V K a ha hanti h0 L s T hs C hC hK z.1 z.2
    have hd := hl.norm_sub_le θ 0
    rw [Real.coe_toNNReal _ hB,Real.norm_eq_abs,Real.norm_eq_abs,sub_zero] at hd
    have hn : N θ z≤N 0 z+B*|θ| := by linarith [le_abs_self (N θ z-N 0 z)]
    simpa only [Real.exp_add] using Real.exp_le_exp.mpr hn
  have hi0 := integrable_exp_finiteCascadeTreeFeatureLogNumerator V K a ha L s 0 T R H
  have hi := norm_integral_le_of_norm_le
    (f:=fun z=>F z*Real.exp (N θ z)*G z)
    (g:=fun z=>(CF*A*Real.exp (B*|θ|))*Real.exp (N 0 z))
    (hi0.const_mul (CF*A*Real.exp (B*|θ|)))
    (Filter.Eventually.of_forall fun z=>by
      rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
      calc
        _≤(CF*(Real.exp (N 0 z)*Real.exp (B*|θ|)))*A :=
          mul_le_mul (mul_le_mul (hFb z) (hExp z) (Real.exp_pos _).le hCF)
            (hGb z) (abs_nonneg _) (by positivity)
        _=_ := by ring)
  rw [integral_const_mul,integral_exp_finiteCascadeTreeFeatureLogNumerator
    V K a ha L s 0 T R H] at hi
  simp only [zero_mul,add_zero] at hi
  simpa only [N,B,Real.norm_eq_abs,mul_assoc,mul_comm,mul_left_comm] using hi

theorem heatC2Datum_finiteCascadeTreeFeatureNumerator
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    FRSB.HeatC2Datum (finiteCascadeTreeFeatureNumerator V K a L s T R H F) := by
  let f := finiteCascadeTreeFeatureNumerator V K a L s T R H F
  let f₁ := finiteCascadeTreeFeatureNumeratorFirst V K a L s T R H F
  let f₂ := finiteCascadeTreeFeatureNumeratorSecond V K a L s T R H F
  let Z := finiteCascadeTreeGaussianNormalizer V a L s j R H
  let B := |(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|
  let D := |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2|
  have hB : 0≤B := abs_nonneg _
  have hD : 0≤D := abs_nonneg _
  have hd (θ : ℝ) : HasDerivAt f (f₁ θ) θ :=
    hasDerivAt_integral_finiteCascadeTreeFeatureNumerator
      V K a ha hanti h0 L s θ T hs R H C hC hK F hF CF hCF hFb
  have hd₁ (θ : ℝ) : HasDerivAt f₁ (f₂ θ) θ :=
    hasDerivAt_integral_finiteCascadeTreeFeatureNumerator_derivative
      V K a ha hanti h0 L s θ T hs R H C hC hK F hF CF hCF hFb
  have he : deriv f=f₁ := funext fun θ=>(hd θ).deriv
  have he₁ : deriv f₁=f₂ := funext fun θ=>(hd₁ θ).deriv
  refine ⟨contDiff_two_finiteCascadeTreeFeatureNumerator
    V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb,?_⟩
  intro i hi
  interval_cases i
  · refine ⟨CF*1*Z,B,hB,fun θ=>?_⟩
    simpa only [iteratedDeriv_zero,mul_one,finiteCascadeTreeFeatureNumerator,f,Z,B] using
      finiteCascadeTreeFeature_factor_integral_growth V K a ha hanti h0 L s θ T hs R H C hC hK
        F (fun _=>1) CF 1 hCF (by norm_num) hFb (fun _=>by norm_num)
  · refine ⟨CF*B*Z,B,hB,fun θ=>?_⟩
    rw [iteratedDeriv_one,he]
    exact finiteCascadeTreeFeature_factor_integral_growth V K a ha hanti h0 L s θ T hs R H C hC hK
      F (fun z=>finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ) CF B hCF hB hFb
      (fun z=>(finiteCascadeTreeFeatureScore_abs_le_of_pointwise
        V a ha hanti h0 L s T hs z.1 K C hC hK z.2 θ).trans (le_abs_self _))
  · refine ⟨CF*(B^2+D)*Z,B,hB,fun θ=>?_⟩
    rw [iteratedDeriv_succ,iteratedDeriv_one,he,he₁]
    exact finiteCascadeTreeFeature_factor_integral_growth V K a ha hanti h0 L s θ T hs R H C hC hK
      F (fun z=>(finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ)^2-
        finiteCascadeTreeFeatureSecondCharge V a L s T z.1 K z.2 θ)
      CF (B^2+D) hCF (by positivity) hFb (fun z=>by
        apply (abs_sub _ _).trans
        apply add_le_add
        · rw [abs_sq]
          have hq : |finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ|≤B := (finiteCascadeTreeFeatureScore_abs_le_of_pointwise
            V a ha hanti h0 L s T hs z.1 K C hC hK z.2 θ).trans (le_abs_self _)
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hq 2
        · exact (finiteCascadeTreeFeatureSecondCharge_abs_le_of_pointwise
            V a ha hanti h0 L s T hs z.1 K C hC hK z.2 θ).trans (le_abs_self _))

end FourPapersCommon
