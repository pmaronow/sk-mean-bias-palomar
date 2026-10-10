module
public import FourPapersCommon.FiniteCascadeTreeFeatureContinuity
public import FRSB.BackwardHeatQuotient

@[expose] public section

/-! The genuine finite tree numerator is C² in a terminal feature. Its
second derivative is continuous by actual dominated convergence of the
recorded density and its vertex Hessian charges. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

def finiteCascadeTreeFeatureNumerator (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ) (θ : ℝ) : ℝ :=
  ∫z,F z*Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)
    ∂finiteCascadeTreeGaussianReferenceLaw L T R H

def finiteCascadeTreeFeatureNumeratorFirst (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ) (θ : ℝ) : ℝ :=
  ∫z,F z*Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)*
    finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ
    ∂finiteCascadeTreeGaussianReferenceLaw L T R H

def finiteCascadeTreeFeatureNumeratorSecond (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ) (θ : ℝ) : ℝ :=
  ∫z,F z*Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)*
    ((finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ)^2-
      finiteCascadeTreeFeatureSecondCharge V a L s T z.1 K z.2 θ)
    ∂finiteCascadeTreeGaussianReferenceLaw L T R H

theorem finiteCascadeTreeFeatureLogNumerator_lipschitz_of_pointwise
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (H : FiniteStateField S) (z : Records (FiniteStateField S) S T) :
    LipschitzWith (|(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|).toNNReal
      (finiteCascadeTreeFeatureLogNumerator V a L s T H K z) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun θ=>(hasDerivAt_finiteCascadeTreeFeatureLogNumerator V a ha L s T H K z θ).differentiableAt)
  intro θ
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ (abs_nonneg _)]
  simpa only [coe_nnnorm,Real.norm_eq_abs,
    (hasDerivAt_finiteCascadeTreeFeatureLogNumerator V a ha L s T H K z θ).deriv] using
    (finiteCascadeTreeFeatureScore_abs_le_of_pointwise V a ha hanti h0 L s T hs H K C hC hK z θ).trans
      (le_abs_self _)

theorem continuous_finiteCascadeTreeFeatureNumeratorSecond
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    Continuous (finiteCascadeTreeFeatureNumeratorSecond V K a L s T R H F) := by
  let P := finiteCascadeTreeGaussianReferenceLaw L T R H
  let N := fun u (z : FiniteStateField S×Records (FiniteStateField S) S T)=>
    finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 u
  let Q := fun u (z : FiniteStateField S×Records (FiniteStateField S) S T)=>
    finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 u
  let E := fun u (z : FiniteStateField S×Records (FiniteStateField S) S T)=>
    finiteCascadeTreeFeatureSecondCharge V a L s T z.1 K z.2 u
  let B := |(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|
  let D := |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2|
  have hB : 0≤B := abs_nonneg _
  have hD : 0≤D := abs_nonneg _
  have hQE (u : ℝ) (z : FiniteStateField S×Records (FiniteStateField S) S T) :
      |(Q u z)^2-E u z|≤B^2+D := by
    apply (abs_sub _ _).trans
    apply add_le_add
    · rw [abs_sq]
      have hq : |Q u z|≤B := (finiteCascadeTreeFeatureScore_abs_le_of_pointwise
        V a ha hanti h0 L s T hs z.1 K C hC hK z.2 u).trans (le_abs_self _)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (Q u z)) hq 2
    · exact (finiteCascadeTreeFeatureSecondCharge_abs_le_of_pointwise
        V a ha hanti h0 L s T hs z.1 K C hC hK z.2 u).trans (le_abs_self _)
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hExp (z : FiniteStateField S×Records (FiniteStateField S) S T) (u : ℝ)
      (hu : u∈Metric.ball θ 1) : Real.exp (N u z)≤Real.exp (N θ z)*Real.exp B := by
    have hl := finiteCascadeTreeFeatureLogNumerator_lipschitz_of_pointwise
      V K a ha hanti h0 L s T hs C hC hK z.1 z.2
    have hd := hl.norm_sub_le u θ
    rw [Real.coe_toNNReal _ hB,Real.norm_eq_abs,Real.norm_eq_abs] at hd
    have huLt : |u-θ|<1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hu
    have hn : N u z≤N θ z+B := by
      have hb := mul_le_mul_of_nonneg_left huLt.le hB
      linarith [le_abs_self (N u z-N θ z)]
    simpa only [Real.exp_add] using Real.exp_le_exp.mpr hn
  have hm (u : ℝ) : AEStronglyMeasurable (fun z=>F z*Real.exp (N u z)*((Q u z)^2-E u z)) P :=
    ((hF.mul (measurable_finiteCascadeTreeFeatureLogNumerator V K a ha L s u T).exp).mul
      ((measurable_finiteCascadeTreeFeatureScore V K a ha L s u T).pow_const 2 |>.sub
        (measurable_finiteCascadeTreeFeatureSecondCharge V K a ha L s u T))).aestronglyMeasurable
  apply continuousAt_of_dominated (μ:=P)
    (.of_forall hm)
    ?_
    ((integrable_exp_finiteCascadeTreeFeatureLogNumerator V K a ha L s θ T R H).const_mul
      (CF*Real.exp B*(B^2+D)))
    (.of_forall fun z=>by
      have hc := continuous_finiteCascadeTreeFeatureSecondNumerator V a ha L s T z.1 K z.2
      simpa only [mul_assoc] using (hc.const_mul (F z)).continuousAt)
  filter_upwards [Metric.ball_mem_nhds θ (by norm_num : (0:ℝ)<1)] with u hu
  exact .of_forall fun z=>by
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _≤(CF*(Real.exp (N θ z)*Real.exp B))*(B^2+D) :=
        mul_le_mul (mul_le_mul (hFb z) (hExp z u hu) (Real.exp_pos _).le hCF)
          (hQE u z) (abs_nonneg _) (by positivity)
      _=_ := by ring

theorem contDiff_two_finiteCascadeTreeFeatureNumerator
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    ContDiff ℝ 2 (finiteCascadeTreeFeatureNumerator V K a L s T R H F) := by
  let f := finiteCascadeTreeFeatureNumerator V K a L s T R H F
  let f₁ := finiteCascadeTreeFeatureNumeratorFirst V K a L s T R H F
  let f₂ := finiteCascadeTreeFeatureNumeratorSecond V K a L s T R H F
  have hd (θ : ℝ) : HasDerivAt f (f₁ θ) θ :=
    hasDerivAt_integral_finiteCascadeTreeFeatureNumerator
      V K a ha hanti h0 L s θ T hs R H C hC hK F hF CF hCF hFb
  have hd₁ (θ : ℝ) : HasDerivAt f₁ (f₂ θ) θ :=
    hasDerivAt_integral_finiteCascadeTreeFeatureNumerator_derivative
      V K a ha hanti h0 L s θ T hs R H C hC hK F hF CF hCF hFb
  have he : deriv f=f₁ := funext fun θ=>(hd θ).deriv
  have he₁ : deriv f₁=f₂ := funext fun θ=>(hd₁ θ).deriv
  have hc₁ : ContDiff ℝ 1 f₁ := contDiff_one_iff_deriv.mpr
    ⟨fun θ=>(hd₁ θ).differentiableAt,he₁ ▸
      continuous_finiteCascadeTreeFeatureNumeratorSecond V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb⟩
  rw [show (2 : ℕ∞ω)=1+1 from rfl,contDiff_succ_iff_deriv]
  exact ⟨fun θ=>(hd θ).differentiableAt,by norm_num,he.symm ▸ hc₁⟩

end FourPapersCommon
