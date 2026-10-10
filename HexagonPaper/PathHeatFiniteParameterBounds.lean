module
public import HexagonPaper.PathHeatFiniteParameterPartials

@[expose] public section

/-! Uniform bounds for actual explicit parameter derivatives of finite
likelihoods. The common constant depends only on the source bounds. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]
variable {n : ℕ}

def pathHeatFiniteParameterGrowthBound (B Dt Dphi C0 : ℝ≥0) : ℝ≥0 :=
  ⟨(1+Dt+Dphi+B*Dt)*Real.exp C0,by positivity⟩

theorem pathHeat_finite_exp_growth_bound
    (A : Field n→L[ℝ]C(X,ℝ)) (ell : C(X,ℝ)→ℝ)
    (C0 C1 K : ℝ≥0) (hA : ‖A‖≤K)
    (hell : ∀p,|ell p|≤C0+C1*‖p‖) (y : Field n) :
    Real.exp (ell (A y))≤Real.exp C0*Real.exp ((C1*K:ℝ≥0)*‖y‖) := by
  have hn : ‖A y‖≤(K:ℝ)*‖y‖ :=
    (A.le_opNorm y).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg y))
  have hv : ell (A y)≤(C0:ℝ)+(C1:ℝ)*(K:ℝ)*‖y‖ := by
    have h := (hell (A y)).trans
      (add_le_add (le_refl (C0:ℝ)) (mul_le_mul_of_nonneg_left hn C1.coe_nonneg))
    exact (le_abs_self _).trans (by simpa only [mul_assoc] using h)
  exact (Real.exp_le_exp.mpr hv).trans_eq (by rw [Real.exp_add];rfl)

theorem pathHeat_source_finite_parameter_bounds
    (A : Field n→L[ℝ]C(X,ℝ))
    (ell Phi : ℝ→C(X,ℝ)→ℝ) (dotell dotPhi : ℝ×C(X,ℝ)→ℝ)
    (S P : ℝ×C(X,ℝ)→SignedMeasure X) (U : Set ℝ) (a : ℝ)
    (hU : U∈𝓝 a) (hEll : PathHeatSignedParameterData ell dotell S U)
    (hPhi : PathHeatSignedParameterData Phi dotPhi P U)
    (B Dt Dphi C0 C1 K : ℝ≥0) (hA : ‖A‖≤K)
    (hell : ∀p,|ell a p|≤C0+C1*‖p‖)
    (hphi : ∀p,|Phi a p|≤B) (hdt : ∀p,|dotell (a,p)|≤Dt)
    (hdphi : ∀p,|dotPhi (a,p)|≤Dphi) (y : Field n) :
    ‖gaussianParameterDerivative (fun z x=>Real.exp (ell z (A x))) a y‖≤
      pathHeatFiniteParameterGrowthBound B Dt Dphi C0*Real.exp ((C1*K:ℝ≥0)*‖y‖) ∧
    ‖gaussianParameterDerivative (fun z x=>Real.exp (ell z (A x))*Phi z (A x)) a y‖≤
      pathHeatFiniteParameterGrowthBound B Dt Dphi C0*Real.exp ((C1*K:ℝ≥0)*‖y‖) := by
  have he := pathHeat_source_finite_exp_parameter_derivatives
    A ell Phi dotell dotPhi S P U a hU hEll hPhi y
  have hg := pathHeat_finite_exp_growth_bound A (ell a) C0 C1 K hA hell y
  have hc1 : (Dt:ℝ)≤1+Dt+Dphi+B*Dt := by
    have := Dphi.coe_nonneg
    have := mul_nonneg B.coe_nonneg Dt.coe_nonneg
    linarith
  have hc2 : (Dphi:ℝ)+(B:ℝ)*Dt≤1+Dt+Dphi+B*Dt := by
    have := Dt.coe_nonneg
    linarith
  have hp : |dotPhi (a,A y)+Phi a (A y)*dotell (a,A y)|≤(Dphi:ℝ)+(B:ℝ)*Dt :=
    (abs_add_le _ _).trans (add_le_add (hdphi (A y)) (by
      rw [abs_mul]
      exact mul_le_mul (hphi (A y)) (hdt (A y)) (abs_nonneg _) B.coe_nonneg))
  constructor
  · rw [he.1,norm_mul,Real.norm_eq_abs,Real.abs_exp,Real.norm_eq_abs]
    calc
      Real.exp (ell a (A y))*|dotell (a,A y)|≤
          (Real.exp C0*Real.exp ((C1*K:ℝ≥0)*‖y‖))*(1+Dt+Dphi+B*Dt) :=
        mul_le_mul hg ((hdt (A y)).trans hc1) (abs_nonneg _) (by positivity)
      _=pathHeatFiniteParameterGrowthBound B Dt Dphi C0*Real.exp ((C1*K:ℝ≥0)*‖y‖) := by
        change _=((1+(Dt:ℝ)+Dphi+B*Dt)*Real.exp C0)*Real.exp ((C1*K:ℝ≥0)*‖y‖)
        ring
  · rw [he.2,norm_mul,Real.norm_eq_abs,Real.abs_exp,Real.norm_eq_abs]
    calc
      Real.exp (ell a (A y))*|dotPhi (a,A y)+Phi a (A y)*dotell (a,A y)|≤
          (Real.exp C0*Real.exp ((C1*K:ℝ≥0)*‖y‖))*(1+Dt+Dphi+B*Dt) :=
        mul_le_mul hg (hp.trans hc2) (abs_nonneg _) (by positivity)
      _=pathHeatFiniteParameterGrowthBound B Dt Dphi C0*Real.exp ((C1*K:ℝ≥0)*‖y‖) := by
        change _=((1+(Dt:ℝ)+Dphi+B*Dt)*Real.exp C0)*Real.exp ((C1*K:ℝ≥0)*‖y‖)
        ring

end HexagonPaper
