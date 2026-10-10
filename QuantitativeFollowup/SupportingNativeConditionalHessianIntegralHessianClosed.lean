module
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralHessianRegularity
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralSquareClosed

@[expose] public section

/-! Actual full-past weighted finite-cell Hessian reaction, including
both physical endpoints and repeated nodes. It is derived from the true
compensated response and the true square-energy identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff BigOperators Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem nativeAnisotropic_finite_compensated_expectation_cropped (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (i : ℕ) (hi : i≤k+1) (a b : ℝ≥0)
    (ha : s.q i≤(a:ℝ)) (hab : a≤b) (hb : (b:ℝ)<s.q (i+1))
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n a] Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    nativeFiniteHessianExpectation D s g w Z b+s.m i*nativeFiniteMeanSquareExpectation D s g w Z b-
      (nativeFiniteHessianExpectation D s g w Z a+s.m i*nativeFiniteMeanSquareExpectation D s g w Z a)=0 := by
  have hZg:=hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hHa:=integrable_nativeFinite_weighted_hessian D s g w Z hZg C hC a
  have hHb:=integrable_nativeFinite_weighted_hessian D s g w Z hZg C hC b
  have hMa:=integrable_nativeFinite_weighted_square D s g w Z hZg C hC a
  have hMb:=integrable_nativeFinite_weighted_square D s g w Z hZg C hC b
  have he:=(nativeAnisotropic_finite_compensated_hessian_cropped D s g w i hi a b ha hab hb Z hZ C hC).2
  have hfun : (fun sample=>Z sample*
      ((nativeAnisotropicFiniteDirectionalHessian D s g w b sample+
        s.m i*(nativeAnisotropicFiniteDirectionalMean D s g w b sample)^2)-
      (nativeAnisotropicFiniteDirectionalHessian D s g w a sample+
        s.m i*(nativeAnisotropicFiniteDirectionalMean D s g w a sample)^2)))=
    fun sample=>(Z sample*nativeAnisotropicFiniteDirectionalHessian D s g w b sample+
      s.m i*(Z sample*(nativeAnisotropicFiniteDirectionalMean D s g w b sample)^2))-
      (Z sample*nativeAnisotropicFiniteDirectionalHessian D s g w a sample+
      s.m i*(Z sample*(nativeAnisotropicFiniteDirectionalMean D s g w a sample)^2)):=by funext sample;ring
  have hsub:=integral_sub (hHb.add (hMb.const_mul (s.m i))) (hHa.add (hMa.const_mul (s.m i)))
  have haddB:=integral_add hHb (hMb.const_mul (s.m i))
  have haddA:=integral_add hHa (hMa.const_mul (s.m i))
  simp only [Pi.add_apply] at hsub haddB haddA
  rw [hfun,hsub,haddB,haddA,integral_const_mul,integral_const_mul] at he
  simpa only [nativeFiniteHessianExpectation,nativeFiniteMeanSquareExpectation,Real.toNNReal_coe] using he

theorem nativeAnisotropic_finite_compensated_expectation_closed (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (i : ℕ) (hi : i≤k+1) (a b : ℝ≥0)
    (ha : s.q i≤(a:ℝ)) (hab : a≤b) (hb : (b:ℝ)≤ s.q (i+1))
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n a] Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    nativeFiniteHessianExpectation D s g w Z b+s.m i*nativeFiniteMeanSquareExpectation D s g w Z b-
      (nativeFiniteHessianExpectation D s g w Z a+s.m i*nativeFiniteMeanSquareExpectation D s g w Z a)=0 := by
  rcases eq_or_lt_of_le hab with heq|hlt
  · subst b
    ring
  have hZg:=hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  let F:=fun r=>nativeFiniteHessianExpectation D s g w Z r+s.m i*nativeFiniteMeanSquareExpectation D s g w Z r
  have hF : Continuous F:=(continuous_nativeFiniteHessianExpectation D s g w Z hZg C hC).add
    ((continuous_nativeFiniteMeanSquareExpectation D s g w Z hZg C hC).const_mul _)
  have hh:=FRSB.closed_interval_increment_bound F (fun _=>0) (fun _=>0) hF
    (fun _ _=>intervalIntegrable_const) (fun _ _=>intervalIntegrable_const)
    (show (a:ℝ)<b from hlt) (fun x y hx hxy hy=>by
      have hx0:=a.coe_nonneg.trans hx.le
      let xN : ℝ≥0:=⟨x,hx0⟩
      let yN : ℝ≥0:=⟨y,hx0.trans hxy⟩
      have hzx : Measurable[vectorBrownianFiltration n xN] Z:=
        hZ.mono ((vectorBrownianFiltration n).mono (show a≤xN from hx.le)) le_rfl
      have he:=nativeAnisotropic_finite_compensated_expectation_cropped D s g w i hi xN yN
        (ha.trans hx.le) (show xN≤yN from hxy) (hy.trans_le hb) Z hzx C hC
      change F y-F x=0 at he
      simp only [intervalIntegral.integral_zero,sub_zero,he,norm_zero,le_refl])
    le_rfl (show (a:ℝ)≤b from hab) le_rfl
  simp only [intervalIntegral.integral_zero,sub_zero] at hh
  exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))

theorem nativeAnisotropic_finite_hessian_expectation_closed (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (i : ℕ) (hi : i≤k+1) (a b : ℝ≥0)
    (ha : s.q i≤(a:ℝ)) (hab : a≤b) (hb : (b:ℝ)≤ s.q (i+1))
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n a] Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    nativeFiniteHessianExpectation D s g w Z b-nativeFiniteHessianExpectation D s g w Z a=
      -(s.m i)*(∫r in (a:ℝ)..(b:ℝ),nativeFiniteNoiseEnergyExpectation D s g w Z r) := by
  have hc:=nativeAnisotropic_finite_compensated_expectation_closed D s g w i hi a b ha hab hb Z hZ C hC
  have hs:=nativeAnisotropic_finite_square_expectation_closed D s g w i hi a b ha hab hb Z hZ C hC
  rw [←hs]
  nlinarith [hc]

end QuantitativeFollowup
