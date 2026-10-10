module
public import FourPapersCommon.FiniteCascadeTreeFeatureDifferentiation

@[expose] public section

/-! Genuine second feature response under the tree reference integral.
The second derivative is obtained by a second dominated differentiation,
with the actual bounded vertex Hessian charge. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem hasDerivAt_integral_finiteCascadeTreeFeatureNumerator_derivative
    (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF) :
    HasDerivAt (fun u=>∫z,F z*Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 u)*
      finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 u
      ∂finiteCascadeTreeGaussianReferenceLaw L T R H)
      (∫z,F z*Real.exp (finiteCascadeTreeFeatureLogNumerator V a L s T z.1 K z.2 θ)*
        ((finiteCascadeTreeFeatureScore V a L s T z.1 K z.2 θ)^2-
          finiteCascadeTreeFeatureSecondCharge V a L s T z.1 K z.2 θ)
        ∂finiteCascadeTreeGaussianReferenceLaw L T R H) θ := by
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
  have hQ (u : ℝ) (z : FiniteStateField S×Records (FiniteStateField S) S T) : |Q u z|≤B :=
    (finiteCascadeTreeFeatureScore_abs_le_of_pointwise V a ha hanti h0 L s T hs z.1 K C hC hK z.2 u).trans
      (le_abs_self _)
  have hE (u : ℝ) (z : FiniteStateField S×Records (FiniteStateField S) S T) : |E u z|≤D :=
    (finiteCascadeTreeFeatureSecondCharge_abs_le_of_pointwise V a ha hanti h0 L s T hs z.1 K C hC hK z.2 u).trans
      (le_abs_self _)
  have hQE (u : ℝ) (z : FiniteStateField S×Records (FiniteStateField S) S T) :
      |(Q u z)^2-E u z|≤B^2+D := by
    apply (abs_sub _ _).trans
    exact add_le_add (by
      rw [abs_sq]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (Q u z)) (hQ u z) 2) (hE u z)
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
    have hn : N u z≤N θ z+B := by
      have hb := mul_le_mul_of_nonneg_left huLt.le hB
      linarith [le_abs_self (N u z-N θ z)]
    simpa only [Real.exp_add] using Real.exp_le_exp.mpr hn
  have hi := integrable_exp_finiteCascadeTreeFeatureLogNumerator V K a ha L s θ T R H
  have hNmeas (u : ℝ) : Measurable (N u) := measurable_finiteCascadeTreeFeatureLogNumerator V K a ha L s u T
  have hQmeas (u : ℝ) : Measurable (Q u) := measurable_finiteCascadeTreeFeatureScore V K a ha L s u T
  have hEmeas (u : ℝ) : Measurable (E u) := measurable_finiteCascadeTreeFeatureSecondCharge V K a ha L s u T
  have hiF : Integrable (fun z=>F z*Real.exp (N θ z)*Q θ z) P :=
    (hi.const_mul (CF*B)).mono'
      ((hF.mul (hNmeas θ).exp).mul (hQmeas θ) |>.aestronglyMeasurable)
      (.of_forall fun z=>by
        rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
        calc
          _≤(CF*Real.exp (N θ z))*B := mul_le_mul
            (mul_le_mul_of_nonneg_right (hFb z) (Real.exp_pos _).le) (hQ θ z)
              (abs_nonneg _) (by positivity)
          _=_ := by ring)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun u z=>F z*Real.exp (N u z)*Q u z)
    (F':=fun u z=>F z*Real.exp (N u z)*((Q u z)^2-E u z))
    (bound:=fun z=>(CF*Real.exp B*(B^2+D))*Real.exp (N θ z))
    (s:=Metric.ball θ 1) (Metric.ball_mem_nhds θ (by norm_num))
    (.of_forall fun u=>(hF.mul (hNmeas u).exp).mul (hQmeas u) |>.aestronglyMeasurable)
    hiF ((hF.mul (hNmeas θ).exp).mul ((hQmeas θ).pow_const 2 |>.sub (hEmeas θ)) |>.aestronglyMeasurable)
    (.of_forall fun z u hu=>by
      rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
      calc
        _≤(CF*(Real.exp (N θ z)*Real.exp B))*(B^2+D) :=
          mul_le_mul (mul_le_mul (hFb z) (hExp z u hu) (Real.exp_pos _).le hCF)
            (hQE u z) (abs_nonneg _) (by positivity)
        _=_ := by ring)
    (hi.const_mul (CF*Real.exp B*(B^2+D)))
    (.of_forall fun z u hu=>by
      simpa only [mul_assoc] using
        (hasDerivAt_finiteCascadeTreeFeatureNumerator_derivative V a ha L s T z.1 K z.2 u).const_mul (F z))).2
  exact hd

end FourPapersCommon
