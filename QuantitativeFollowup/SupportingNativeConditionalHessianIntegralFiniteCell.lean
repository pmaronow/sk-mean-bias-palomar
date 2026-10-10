module
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralSquareCell
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralResponse
public import QuantitativeFollowup.AnisotropicWhitenedFiniteState
public import QuantitativeFollowup.AnisotropicProcessEnergy

@[expose] public section

/-! Actual finite anisotropic field-feature square evolution. The native
Hessian noise energy is computed from the true second differential, and
all drift and response identifications are discharged for this model. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def nativeAnisotropicFiniteDirectionalMean (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (w : Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  fderiv ℝ (anisotropicFiniteTailPotential D s (projIcc (0:ℝ) 1 zero_le_one r))
    (anisotropicDisorderInjection n g+
      anisotropicUnitInput D (anisotropicWhitenedFiniteState D s g r sample))
    (anisotropicFieldInjection n w)

def nativeAnisotropicFiniteDirectionalNoiseEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (w : Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  ∑l : Fin n,(fderiv ℝ (fderiv ℝ
      (anisotropicFiniteTailPotential D s (projIcc (0:ℝ) 1 zero_le_one r)))
    (anisotropicDisorderInjection n g+
      anisotropicUnitInput D (anisotropicWhitenedFiniteState D s g r sample))
    (anisotropicUnitInput D (EuclideanSpace.single l 1)) (anisotropicFieldInjection n w))^2

theorem nativeAnisotropicFiniteDirectionalNoiseEnergy_nonneg (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) :
    0≤nativeAnisotropicFiniteDirectionalNoiseEnergy D s g w r sample :=
  Finset.sum_nonneg fun _ _=>sq_nonneg _

theorem nativeAnisotropic_finite_directional_square_cropped (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (i : ℕ) (hi : i≤k+1) (a b : ℝ≥0)
    (ha : s.q i≤(a:ℝ)) (hab : a≤b) (hb : (b:ℝ)<s.q (i+1))
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n a] Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*((nativeAnisotropicFiniteDirectionalMean D s g w b sample)^2-
      (nativeAnisotropicFiniteDirectionalMean D s g w a sample)^2)) (vectorDisorderBrownianMeasure n) ∧
    (∫sample,Z sample*((nativeAnisotropicFiniteDirectionalMean D s g w b sample)^2-
      (nativeAnisotropicFiniteDirectionalMean D s g w a sample)^2)∂vectorDisorderBrownianMeasure n)=
      ∫sample,(∫r in Ioc a b,Z sample*nativeAnisotropicFiniteDirectionalNoiseEnergy D s g w r sample
        ∂nonnegativeLebesgueMeasure)∂vectorDisorderBrownianMeasure n := by
  let X:=anisotropicWhitenedFiniteState D s g
  let d:=vectorAdditiveDrift (anisotropicWhitenedFiniteDriftData D s g) 1 0 1
  let F:=anisotropicWhitenedFiniteJointPotential D s (k+1-i) g
  let G:=nativeAnisotropicWhitenedJointFieldResponse D s (k+1-i) g w
  let data:=nativeAnisotropicFieldResponseData D s (k+1-i) g w
  have hr1 {r : ℝ≥0} (hrb : r≤b) : (r:ℝ)≤1:=
    (show (r:ℝ)≤b from hrb).trans (hb.le.trans (s.q_le_one (by omega)))
  have hR {r : ℝ≥0} (har : a≤r) (hrb : r≤b) (sample : VectorDisorderBrownianSample n) :
      vectorJointResponse F G (1*(s.q (i+1)-r)) (s.m i) (sample.1,X r sample)=
        nativeAnisotropicFiniteDirectionalMean D s g w r sample := by
    let qr:=projIcc (0:ℝ) 1 zero_le_one (r:ℝ)
    have hqr : (qr:ℝ)=(r:ℝ):=congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨r.coe_nonneg,hr1 hrb⟩)
    have hcell : (qr:ℝ)∈Icc (s.q i) (s.q (i+1)):=by
      rw [hqr]
      exact ⟨ha.trans (show (a:ℝ)≤r from har),(show (r:ℝ)≤b from hrb).trans hb.le⟩
    change vectorStepResponse (1*(s.q (i+1)-r)) (s.m i)
      (anisotropicWhitenedFinitePotential D s (k+1-i) g)
      (fun y=>nativeAnisotropicWhitenedJointFieldResponse D s (k+1-i) g w (sample.1,y))
      (X r sample)=_
    have hG : (fun y=>nativeAnisotropicWhitenedJointFieldResponse D s (k+1-i) g w (sample.1,y))=
        (fun y=>nativeAnisotropicWhitenedJointFieldResponse D s (k+1-i) g w (0,y)):=rfl
    rw [hG,one_mul,←hqr]
    exact nativeAnisotropic_step_response_eq_field_derivative D s g w qr i hi hcell _
  have hc:=vectorItoCharacteristics_anisotropicWhitenedFiniteState D s g
  have he:=native_jointResponse_square_interval_past data (m:=s.m i) hc (by norm_num : (1:ℝ)^2=1)
    (by norm_num : (0:ℝ)<1) a b hab hb Z hZ C hC
  have hfun : (fun sample=>Z sample*((vectorJointResponse F G (1*(s.q (i+1)-b)) (s.m i)
      (sample.1,X b sample))^2-(vectorJointResponse F G (1*(s.q (i+1)-a)) (s.m i)
      (sample.1,X a sample))^2))=
      (fun sample=>Z sample*((nativeAnisotropicFiniteDirectionalMean D s g w b sample)^2-
        (nativeAnisotropicFiniteDirectionalMean D s g w a sample)^2)):=by
    funext sample
    rw [hR hab le_rfl,hR le_rfl hab]
  refine ⟨he.1.congr (.of_forall fun sample=>congrFun hfun sample),?_⟩
  rw [hfun] at he
  rw [he.2]
  apply integral_congr_ae
  filter_upwards with sample
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have hcell : (r:ℝ)∈Ioo (s.q i) (s.q (i+1)):=
    ⟨ha.trans_lt (show (a:ℝ)<r from hr.1),(show (r:ℝ)≤b from hr.2).trans_lt hb⟩
  have hd:=anisotropicWhitenedFinite_actual_cell_drift D s g i hi r hcell sample
  have hFc : (fun x=>F (sample.1,x))=
      anisotropicWhitenedFinitePotential D s (k+1-i) g := by
    funext x
    rfl
  rw [native_jointResponse_square_source_drift_cancellation F G (s.m i) 1 (s.q (i+1)) X d r sample
    (by rw [hFc,one_smul,one_mul];exact hd),one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  let qr:=projIcc (0:ℝ) 1 zero_le_one (r:ℝ)
  have hqr : (qr:ℝ)=(r:ℝ):=congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨r.coe_nonneg,hr1 hr.2⟩)
  have hqc : (qr:ℝ)∈Icc (s.q i) (s.q (i+1)):=by simpa only [hqr] using ⟨hcell.1.le,hcell.2.le⟩
  have hG : (fun y=>G (sample.1,y))=
      (fun y=>nativeAnisotropicWhitenedJointFieldResponse D s (k+1-i) g w (0,y)):=rfl
  change (fderiv ℝ (vectorStepResponse (1*(s.q (i+1)-r)) (s.m i)
    (anisotropicWhitenedFinitePotential D s (k+1-i) g) (fun y=>G (sample.1,y)))
    (X r sample) (EuclideanSpace.single l 1))^2=_
  rw [hG,one_mul,←hqr,nativeAnisotropic_step_response_spatial_derivative D s g w qr i hi hqc]
  rw [projIcc_of_mem zero_le_one qr.property]

end QuantitativeFollowup
