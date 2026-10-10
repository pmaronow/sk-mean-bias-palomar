module
public import FourPapersCommon.FiniteCascadeTreeFeatureIntegral
public import FourPapersCommon.FiniteCascadeTreeFeatureMeasurability
public import FourPapersCommon.FiniteCascadeTreeUniformFeatures

@[expose] public section

/-! Dominated differentiation of the actual feature-perturbed tree
numerator. The integrable envelope comes from the true density at the
base parameter and the genuine global score bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem hasDerivAt_integral_finiteCascadeTreeFeatureNumerator
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    HasDerivAt (fun u=>∫z,F z*Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 u)
      ∂finiteCascadeTreeGaussianReferenceLaw L T R H)
      (∫z,F z*Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)*
        finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ
        ∂finiteCascadeTreeGaussianReferenceLaw L T R H) θ := by
  let P := finiteCascadeTreeGaussianReferenceLaw L T R H
  let N := fun u (z : FiniteStateField S×Records (FiniteStateField S) S T)=>
    finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 u
  let Q := fun u (z : FiniteStateField S×Records (FiniteStateField S) S T)=>
    finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 u
  let B := |(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|
  have hB : 0≤B := abs_nonneg _
  have hQ (u : ℝ) (z : FiniteStateField S×Records (FiniteStateField S) S T) : |Q u z|≤B :=
    (finiteCascadeTreeFeatureScore_abs_le_of_pointwise V a ha hanti h0 L s T hs z.1 K C hC hK z.2 u).trans
      (le_abs_self _)
  have hLip (z : FiniteStateField S×Records (FiniteStateField S) S T) :
      LipschitzWith B.toNNReal (fun u=>N u z) := by
    apply lipschitzWith_of_nnnorm_deriv_le
      (fun u=>(hasDerivAt_finiteCascadeTreeFeatureLogNumerator V a ha L s T z.1 K z.2 u).differentiableAt)
    intro u
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hB]
    simpa only [coe_nnnorm,Real.norm_eq_abs,
      (hasDerivAt_finiteCascadeTreeFeatureLogNumerator V a ha L s T z.1 K z.2 u).deriv] using hQ u z
  have hExp (z : FiniteStateField S×Records (FiniteStateField S) S T) (u : ℝ)
      (hu : u∈Metric.ball θ 1) : Real.exp (N u z)≤Real.exp (N θ z)*Real.exp B := by
    have hd := (hLip z).norm_sub_le u θ
    rw [Real.coe_toNNReal _ hB,Real.norm_eq_abs,Real.norm_eq_abs] at hd
    have huLt : |u-θ|<1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hu
    have hu' : |u-θ|≤1 := huLt.le
    have hn : N u z≤N θ z+B := by
      have hb := mul_le_mul_of_nonneg_left hu' hB
      linarith [le_abs_self (N u z-N θ z)]
    simpa only [Real.exp_add] using Real.exp_le_exp.mpr hn
  have hi := integrable_exp_finiteCascadeTreeFeatureLogNumerator V K a ha L s θ T R H
  have hNmeas (u : ℝ) : Measurable (N u) := measurable_finiteCascadeTreeFeatureLogNumerator V K a ha L s u T
  have hQmeas (u : ℝ) : Measurable (Q u) := measurable_finiteCascadeTreeFeatureScore V K a ha L s u T
  have hiF : Integrable (fun z=>F z*Real.exp (N θ z)) P :=
    (hi.const_mul CF).mono' ((hF.mul (hNmeas θ).exp).aestronglyMeasurable)
      (.of_forall fun z=>by
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hFb z) (Real.exp_pos _).le)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun u z=>F z*Real.exp (N u z))
    (F':=fun u z=>F z*Real.exp (N u z)*Q u z)
    (bound:=fun z=>(CF*Real.exp B*B)*Real.exp (N θ z))
    (s:=Metric.ball θ 1) (Metric.ball_mem_nhds θ (by norm_num))
    (.of_forall fun u=>(hF.mul (hNmeas u).exp).aestronglyMeasurable)
    hiF ((hF.mul (hNmeas θ).exp).mul (hQmeas θ) |>.aestronglyMeasurable)
    (.of_forall fun z u hu=>by
      rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
      calc
        _≤(CF*(Real.exp (N θ z)*Real.exp B))*B :=
          mul_le_mul (mul_le_mul (hFb z) (hExp z u hu) (Real.exp_pos _).le hCF)
            (hQ u z) (abs_nonneg _) (by positivity)
        _=_ := by ring)
    (hi.const_mul (CF*Real.exp B*B))
    (.of_forall fun z u hu=>by
      simpa only [mul_assoc] using
        (hasDerivAt_finiteCascadeTreeFeatureNumerator V a ha L s T z.1 K z.2 u).const_mul (F z))).2
  exact hd

end FourPapersCommon
