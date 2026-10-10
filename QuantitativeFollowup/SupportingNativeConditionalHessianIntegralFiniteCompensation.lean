module
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralHessianObservable
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralFiniteCell
public import QuantitativePaper.VectorJointResponseIntervalPast

@[expose] public section

/-! The literal finite anisotropic Hessian plus the cell mass times the
field-feature mean square is a genuine backward response in the whole
Wiener past. No conditional-response identity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def nativeAnisotropicFiniteDirectionalHessian (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (w : Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s
    (projIcc (0:ℝ) 1 zero_le_one r)))
    (anisotropicDisorderInjection n g+anisotropicUnitInput D (anisotropicWhitenedFiniteState D s g r sample))
    (anisotropicFieldInjection n w) (anisotropicFieldInjection n w)

theorem nativeAnisotropic_finite_compensated_hessian_cropped (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (i : ℕ) (hi : i≤k+1) (a b : ℝ≥0)
    (ha : s.q i≤(a:ℝ)) (hab : a≤b) (hb : (b:ℝ)<s.q (i+1))
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n a] Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*
      ((nativeAnisotropicFiniteDirectionalHessian D s g w b sample+
        s.m i*(nativeAnisotropicFiniteDirectionalMean D s g w b sample)^2)-
      (nativeAnisotropicFiniteDirectionalHessian D s g w a sample+
        s.m i*(nativeAnisotropicFiniteDirectionalMean D s g w a sample)^2)))
      (vectorDisorderBrownianMeasure n) ∧
    (∫sample,Z sample*
      ((nativeAnisotropicFiniteDirectionalHessian D s g w b sample+
        s.m i*(nativeAnisotropicFiniteDirectionalMean D s g w b sample)^2)-
      (nativeAnisotropicFiniteDirectionalHessian D s g w a sample+
        s.m i*(nativeAnisotropicFiniteDirectionalMean D s g w a sample)^2))
      ∂vectorDisorderBrownianMeasure n)=0 := by
  let X:=anisotropicWhitenedFiniteState D s g
  let d:=vectorAdditiveDrift (anisotropicWhitenedFiniteDriftData D s g) 1 0 1
  let F:=anisotropicWhitenedFiniteJointPotential D s (k+1-i) g
  let G:=nativeAnisotropicWhitenedJointCompensatedHessian D s i g w
  let data:=nativeAnisotropicCompensatedHessianResponseData D s i g w
  have hr1 {r : ℝ≥0} (hrb : r≤b) : (r:ℝ)≤1:=
    (show (r:ℝ)≤b from hrb).trans (hb.le.trans (s.q_le_one (by omega)))
  have hR {r : ℝ≥0} (har : a≤r) (hrb : r≤b) (sample : VectorDisorderBrownianSample n) :
      vectorJointResponse F G (1*(s.q (i+1)-r)) (s.m i) (sample.1,X r sample)=
      nativeAnisotropicFiniteDirectionalHessian D s g w r sample+
        s.m i*(nativeAnisotropicFiniteDirectionalMean D s g w r sample)^2 := by
    let qr:=projIcc (0:ℝ) 1 zero_le_one (r:ℝ)
    have hqr : (qr:ℝ)=(r:ℝ):=congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨r.coe_nonneg,hr1 hrb⟩)
    have hcell : (qr:ℝ)∈Icc (s.q i) (s.q (i+1)):=by
      rw [hqr]
      exact ⟨ha.trans (show (a:ℝ)≤r from har),(show (r:ℝ)≤b from hrb).trans hb.le⟩
    have he:=nativeAnisotropic_compensated_hessian_response D s g w qr i hi hcell (X r sample)
    rw [hqr] at he
    change vectorStepResponse (1*(s.q (i+1)-r)) (s.m i)
      (anisotropicWhitenedFinitePotential D s (k+1-i) g)
      (fun z=>nativeAnisotropicWhitenedJointCompensatedHessian D s i g w (sample.1,z)) (X r sample)=_
    rw [one_mul]
    exact he
  have hc:=vectorItoCharacteristics_anisotropicWhitenedFiniteState D s g
  have he:=vector_jointResponse_interval_martingale_past data (m:=s.m i) hc
    (by norm_num : (1:ℝ)^2=1) (by norm_num : (0:ℝ)<1) a b hab hb (fun r hr sample=>by
      have hcell : (r:ℝ)∈Ioo (s.q i) (s.q (i+1)):=
        ⟨ha.trans_lt (show (a:ℝ)<r from hr.1),(show (r:ℝ)≤b from hr.2).trans_lt hb⟩
      have hFc : (fun x=>F (sample.1,x))=anisotropicWhitenedFinitePotential D s (k+1-i) g:=by
        funext x;rfl
      rw [hFc,one_smul,one_mul]
      exact anisotropicWhitenedFinite_actual_cell_drift D s g i hi r hcell sample) Z hZ C hC
  have hfun : (fun sample=>Z sample*(vectorJointResponse F G (1*(s.q (i+1)-b)) (s.m i)
      (sample.1,X b sample)-vectorJointResponse F G (1*(s.q (i+1)-a)) (s.m i) (sample.1,X a sample)))=
      (fun sample=>Z sample*
        ((nativeAnisotropicFiniteDirectionalHessian D s g w b sample+
          s.m i*(nativeAnisotropicFiniteDirectionalMean D s g w b sample)^2)-
        (nativeAnisotropicFiniteDirectionalHessian D s g w a sample+
          s.m i*(nativeAnisotropicFiniteDirectionalMean D s g w a sample)^2))):=by
    funext sample
    rw [hR hab le_rfl,hR le_rfl hab]
  rw [hfun] at he
  exact he

end QuantitativeFollowup
