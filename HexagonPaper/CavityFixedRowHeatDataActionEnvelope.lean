module
public import HexagonPaper.CavityFixedRowHeatDataNativeIntegral
public import QuantitativePaper.ExponentialJetBounds

@[expose] public section

/-! Uniform actual exponential jets of the native root-plus-tree relative
action. The deterministic source charge and terminal linear bound control
all retained field configurations. -/
noncomputable section
open Set Filter MeasureTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ContDiff BigOperators NNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n m : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

def cavityNativeChargeRelativeAction (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (ν : Measure X) (A : C(X,Paper.Overlap×AnisotropicParameter n))
    (L : Field m→L[ℝ]AnisotropicParameter n) (ℓ : Field m→L[ℝ]ℝ) (θ : Field m) : ℝ :=
  ℓ θ-(cavityNativeChargePotential D μ ν A L θ-cavityNativeChargePotential D μ ν A L 0)

 theorem cavityNativeChargeRelativeAction_zero (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (ν : Measure X) (A : C(X,Paper.Overlap×AnisotropicParameter n))
    (L : Field m→L[ℝ]AnisotropicParameter n) (ℓ : Field m→L[ℝ]ℝ) :
    cavityNativeChargeRelativeAction D μ ν A L ℓ 0=0 := by
  simp [cavityNativeChargeRelativeAction]

 theorem cavityNativeChargeRelativeAction_smooth (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (ν : Measure X) [IsFiniteMeasure ν] (A : C(X,Paper.Overlap×AnisotropicParameter n))
    (L : Field m→L[ℝ]AnisotropicParameter n) (ℓ : Field m→L[ℝ]ℝ) :
    ContDiff ℝ ∞ (cavityNativeChargeRelativeAction D μ ν A L ℓ) :=
  ℓ.contDiff.sub ((cavityNativeChargePotential_smooth D μ ν A L).sub contDiff_const)

 theorem cavityNativeChargeRelativeAction_positive_jet_bound (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (ν : Measure X) [IsFiniteMeasure ν] (A : C(X,Paper.Overlap×AnisotropicParameter n))
    (L : Field m→L[ℝ]AnisotropicParameter n) (ℓ : Field m→L[ℝ]ℝ)
    (b : ℝ) (hb : 1 ≤ b) (hℓ : ‖ℓ‖ ≤ b) (r : ℕ) (hr : 1 ≤ r) (θ : Field m) :
    ‖iteratedFDeriv ℝ r (cavityNativeChargeRelativeAction D μ ν A L ℓ) θ‖ ≤ b^r+ν.real univ*(cavityTreeUniformParameterJetBound n r*‖L‖^r) := by
  let f:=cavityNativeChargePotential D μ ν A L
  have hf : ContDiff ℝ ∞ f:=cavityNativeChargePotential_smooth D μ ν A L
  change ‖iteratedFDeriv ℝ r ((ℓ : Field m→ℝ)-(f-fun _=>f 0)) θ‖ ≤ _
  have he:=iteratedFDeriv_sub_apply (𝕜:=ℝ) (i:=r) (x:=θ)
    (f:=(ℓ : Field m→ℝ)) (g:=f-fun _=>f 0)
    ℓ.contDiff.contDiffAt
    ((hf.sub contDiff_const).of_le (by simp)).contDiffAt
  have he2:=iteratedFDeriv_sub_apply (𝕜:=ℝ) (i:=r) (x:=θ)
    (f:=f) (g:=fun _=>f 0) (hf.of_le (by simp)).contDiffAt contDiffAt_const
  rw [he,he2,iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply,sub_zero]
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_iteratedFDeriv_linear_le ℓ b hb hℓ hr θ)
    (cavityNativeChargePotential_positive_jet_bound D μ ν A L r hr θ))

set_option backward.isDefEq.respectTransparency.types true in
 theorem cavityNativeChargeRelativeAction_exp_uniform_two_jets (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (ν : Measure X) [IsFiniteMeasure ν] (L : Field m→L[ℝ]AnisotropicParameter n)
    (b : ℝ) (hb : 1 ≤ b) :
    ∃C R : ℝ,0 ≤ C ∧ 0 ≤ R ∧
      ∀(A : C(X,Paper.Overlap×AnisotropicParameter n)) (ℓ : Field m→L[ℝ]ℝ),‖ℓ‖ ≤ b→
      ∀r,r ≤ 2→∀θ,‖iteratedFDeriv ℝ r
        (fun y=>Real.exp (cavityNativeChargeRelativeAction D μ ν A L ℓ y)) θ‖ ≤ C*Real.exp (R*‖θ‖) := by
  let B:=fun r=>b^r+ν.real univ*(cavityTreeUniformParameterJetBound n r*‖L‖^r)
  let K:=max 1 (|B 1|+|B 2|)
  have hK : 1 ≤ K:=le_max_left _ _
  have hB (r : ℕ) (hr : 1 ≤ r) (hr2 : r ≤ 2) : B r ≤ K^r := by
    have hh : B r ≤ |B 1|+|B 2|:=by
      interval_cases r
      · exact (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
      · exact (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
    exact hh.trans ((le_max_right _ _).trans (le_self_pow₀ hK (by omega)))
  refine ⟨2*K^2,K,by positivity,zero_le_one.trans hK,?_⟩
  intro A ℓ hℓ r hr θ
  let f:=cavityNativeChargeRelativeAction D μ ν A L ℓ
  have hf : ContDiff ℝ ∞ f:=cavityNativeChargeRelativeAction_smooth D μ ν A L ℓ
  have hj (i : ℕ) (hi : 1 ≤ i) (hi2 : i ≤ 2) (y : Field m) :
      ‖iteratedFDeriv ℝ i f y‖ ≤ K^i:=
    (cavityNativeChargeRelativeAction_positive_jet_bound D μ ν A L ℓ b hb hℓ i hi y).trans (hB i hi hi2)
  let κ : ℝ≥0:=⟨K,zero_le_one.trans hK⟩
  have hκ : (κ:ℝ)=K:=rfl
  have hl : LipschitzWith κ f :=
    lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) (fun y=>by
      apply (show ‖fderiv ℝ f y‖₊ ≤ ⟨K,zero_le_one.trans hK⟩ ↔ ‖fderiv ℝ f y‖ ≤ K from NNReal.coe_le_coe.symm).mpr
      simpa only [norm_iteratedFDeriv_one,pow_one] using hj 1 le_rfl (by omega) y)
  have hv : f θ ≤ K*‖θ‖:=by
    have hn:=hl.norm_sub_le θ 0
    have hz : f 0=0:=cavityNativeChargeRelativeAction_zero D μ ν A L ℓ
    rw [hz,sub_zero,sub_zero,hκ] at hn
    have ha:=le_abs_self (f θ)
    simp only [Real.norm_eq_abs] at hn
    linarith only [ha,hn]
  have he:=norm_iteratedFDeriv_exp_mul_le f (hf.of_le (by simp : (2:WithTop ℕ∞) ≤ ∞)) hr 1 K θ
    (fun i hi hir=>hj i hi (hir.trans hr) θ)
  simp only [one_mul,abs_one,max_self,one_pow,mul_one] at he
  have hfac : (r.factorial:ℝ) ≤ 2:=by interval_cases r <;> norm_num
  have hpow : K^r ≤ K^2:=pow_le_pow_right₀ hK hr
  apply he.trans
  have hm:=mul_le_mul (mul_le_mul_of_nonneg_right hfac (Real.exp_pos (f θ)).le) hpow
    (pow_nonneg (zero_le_one.trans hK) _) (by positivity)
  have hex:=Real.exp_le_exp.mpr hv
  nlinarith [mul_le_mul_of_nonneg_left hex (by positivity : 0 ≤ 2*K^2)]

end HexagonPaper
