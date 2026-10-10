module
public import QuantitativeFollowup.AnisotropicMeasureState
public import QuantitativeFollowup.AnisotropicTailHessian
public import QuantitativeFollowup.AnisotropicFieldDerivative

@[expose] public section

/-! Exact diagonal whitening of the actual anisotropic potential and state.
The inverse is constructed from the model's strictly positive variances;
the transformed state is driven by the original standard Wiener coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal ContDiff Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 800000

def anisotropicInverseNoiseMap (D : AnisotropicSpinModel n) : Field n→L[ℝ]Field n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x=>WithLp.toLp 2 (fun i=>(Real.sqrt (D.variance i))⁻¹*x i)
      map_add' := by intro x y;ext i;simp only [PiLp.add_apply,mul_add]
      map_smul' := by intro c x;ext i;simp only [PiLp.smul_apply,smul_eq_mul,RingHom.id_apply];ring }

@[simp] theorem anisotropicInverseNoiseMap_apply (D : AnisotropicSpinModel n)
    (x : Field n) (i : Fin n) :
    anisotropicInverseNoiseMap D x i=(Real.sqrt (D.variance i))⁻¹*x i := rfl

@[simp] theorem anisotropicInverseNoiseMap_noise (D : AnisotropicSpinModel n) (x : Field n) :
    anisotropicInverseNoiseMap D (anisotropicNoiseMap D x)=x := by
  ext i
  simp only [anisotropicInverseNoiseMap_apply,anisotropicNoiseMap_apply,←mul_assoc,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (D.variance_pos i)).ne',one_mul]

@[simp] theorem anisotropicNoiseMap_inverseNoise (D : AnisotropicSpinModel n) (x : Field n) :
    anisotropicNoiseMap D (anisotropicInverseNoiseMap D x)=x := by
  ext i
  simp only [anisotropicInverseNoiseMap_apply,anisotropicNoiseMap_apply,←mul_assoc,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (D.variance_pos i)).ne',one_mul]

def anisotropicNoiseEquiv (D : AnisotropicSpinModel n) : Field n≃L[ℝ]Field n where
  toLinearEquiv := {
    toLinearMap := (anisotropicNoiseMap D).toLinearMap
    invFun := anisotropicInverseNoiseMap D
    left_inv := anisotropicInverseNoiseMap_noise D
    right_inv := anisotropicNoiseMap_inverseNoise D }
  continuous_toFun := (anisotropicNoiseMap D).continuous
  continuous_invFun := (anisotropicInverseNoiseMap D).continuous

@[simp] theorem anisotropicInverseNoiseMap_variance (D : AnisotropicSpinModel n)
    (x : Field n) : anisotropicInverseNoiseMap D (anisotropicVarianceMap D x)=anisotropicNoiseMap D x :=
  anisotropicInverseNoiseMap_noise D (anisotropicNoiseMap D x)

theorem anisotropicNoiseMap_selfAdjoint (D : AnisotropicSpinModel n) (x y : Field n) :
    inner ℝ (anisotropicNoiseMap D x) y=inner ℝ x (anisotropicNoiseMap D y) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,anisotropicNoiseMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fderiv_anisotropicMeasureTailPotential_field (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) (w : Field n) :
    fderiv ℝ (anisotropicMeasureTailPotential D μ q) P (anisotropicFieldInjection n w)=
      inner ℝ (anisotropicMeasureTailMagnetization D μ q P) w := by
  rw [anisotropicFieldDirection_sum,map_sum]
  simp_rw [map_smul,smul_eq_mul]
  change (∑i : Fin n,w i*anisotropicMeasureTailMagnetization D μ q P i)=_
  simp [PiLp.inner_apply,RCLike.inner_apply,mul_comm]

def anisotropicWhitenedTailPotential (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (g : AnisotropicDisorder n) (y : Field n) : ℝ :=
  anisotropicMeasureTailPotential D μ q
    (anisotropicDisorderInjection n g+anisotropicFieldInjection n (anisotropicNoiseMap D y))

theorem contDiff_anisotropicWhitenedTailPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (g : AnisotropicDisorder n) :
    ContDiff ℝ 2 (anisotropicWhitenedTailPotential D μ q g) :=
  (anisotropicMeasureTailPotential_hessian_limit D μ q).2.comp
    (contDiff_const.add ((anisotropicFieldInjection n).contDiff.comp (anisotropicNoiseMap D).contDiff))

theorem gradient_anisotropicWhitenedTailPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (g : AnisotropicDisorder n) (y : Field n) :
    gradient (anisotropicWhitenedTailPotential D μ q g) y=
      anisotropicNoiseMap D (anisotropicMeasureTailMagnetization D μ q
        (anisotropicDisorderInjection n g+anisotropicFieldInjection n (anisotropicNoiseMap D y))) := by
  let P := anisotropicDisorderInjection n g+anisotropicFieldInjection n (anisotropicNoiseMap D y)
  have hd := (anisotropicMeasureTailPotential_derivative_limit D μ q).2.differentiable_one
  have hc : HasFDerivAt (fun z : Field n=>anisotropicDisorderInjection n g+
      anisotropicFieldInjection n (anisotropicNoiseMap D z))
      ((anisotropicFieldInjection n).comp (anisotropicNoiseMap D)) y :=
    (((anisotropicFieldInjection n).comp (anisotropicNoiseMap D)).hasFDerivAt.const_add _)
  have he := ((hd P).hasFDerivAt.comp y hc).fderiv
  apply (InnerProductSpace.toDual ℝ (Field n)).injective
  ext w
  rw [toDual_gradient]
  change fderiv ℝ (anisotropicMeasureTailPotential D μ q ∘
    (fun z : Field n=>anisotropicDisorderInjection n g+anisotropicFieldInjection n (anisotropicNoiseMap D z))) y w=
    inner ℝ (anisotropicNoiseMap D (anisotropicMeasureTailMagnetization D μ q P)) w
  rw [he,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    fderiv_anisotropicMeasureTailPotential_field,←anisotropicNoiseMap_selfAdjoint]

def anisotropicWhitenedState (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (r : ℝ) (sample : AnisotropicDisorderBrownianSample n) : Field n :=
  anisotropicInverseNoiseMap D (anisotropicMeasureState D μ r sample)

theorem continuous_anisotropicWhitenedState (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (sample : AnisotropicDisorderBrownianSample n) :
    Continuous (fun r=>anisotropicWhitenedState D μ r sample) :=
  (anisotropicInverseNoiseMap D).continuous.comp (continuous_anisotropicMeasureState D μ sample)

theorem anisotropicWhitenedState_equation (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (r : ℝ) (hr : r∈Icc (0 : ℝ) 1) (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicWhitenedState D μ r sample=vectorBrownian r.toNNReal sample.2+
      ∫s in 0..r,Paper.parisiCDF μ s • gradient
        (anisotropicWhitenedTailPotential D μ (projIcc (0 : ℝ) 1 zero_le_one s) sample.1)
        (anisotropicWhitenedState D μ s sample) := by
  rw [anisotropicWhitenedState,anisotropicMeasureState_equation D μ sample r hr,map_add,
    anisotropicInverseNoiseMap_noise]
  have hi : (anisotropicNoiseEquiv D).symm (∫s in 0..r,
      Paper.parisiCDF μ s • anisotropicVarianceMap D
        (anisotropicMeasureTailMagnetization D μ (projIcc (0 : ℝ) 1 zero_le_one s)
          (anisotropicDisorderInjection n sample.1+
            anisotropicFieldInjection n (anisotropicMeasureState D μ s sample))))=
      ∫s in 0..r,(anisotropicNoiseEquiv D).symm
        (Paper.parisiCDF μ s • anisotropicVarianceMap D
          (anisotropicMeasureTailMagnetization D μ (projIcc (0 : ℝ) 1 zero_le_one s)
            (anisotropicDisorderInjection n sample.1+
              anisotropicFieldInjection n (anisotropicMeasureState D μ s sample)))) := by
    simpa only [intervalIntegral.integral_of_le hr.1] using
      ((anisotropicNoiseEquiv D).symm.integral_comp_comm (μ:=volume.restrict (Ioc 0 r)) _).symm
  change _+ (anisotropicNoiseEquiv D).symm (∫s in 0..r,_) = _
  rw [hi]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  change anisotropicInverseNoiseMap D (_ • anisotropicVarianceMap D _)=_
  rw [map_smul,anisotropicInverseNoiseMap_variance]
  simp only [gradient_anisotropicWhitenedTailPotential,anisotropicWhitenedState,anisotropicNoiseMap_inverseNoise]

end QuantitativeFollowup
