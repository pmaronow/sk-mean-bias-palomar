module
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralEnergyRegularity
public import FRSB.ClosedIntervalBounds

@[expose] public section

/-! Genuine weighted directional square identity on both closed finite
cell endpoints. All source integrability and expectation continuity follow
from the actual profile-independent Hessian bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff BigOperators Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def nativeFiniteMeanSquareExpectation (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (w : Field n) (Z : VectorDisorderBrownianSample n→ℝ) (r : ℝ) : ℝ :=
  ∫sample,Z sample*(nativeAnisotropicFiniteDirectionalMean D s g w r.toNNReal sample)^2
    ∂vectorDisorderBrownianMeasure n

def nativeFiniteNoiseEnergyExpectation (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (w : Field n) (Z : VectorDisorderBrownianSample n→ℝ) (r : ℝ) : ℝ :=
  ∫sample,Z sample*nativeAnisotropicFiniteDirectionalNoiseEnergy D s g w r.toNNReal sample
    ∂vectorDisorderBrownianMeasure n

theorem integrable_nativeFinite_weighted_square (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (w : Field n) (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) (r : ℝ≥0) :
    Integrable (fun sample=>Z sample*(nativeAnisotropicFiniteDirectionalMean D s g w r sample)^2)
      (vectorDisorderBrownianMeasure n) := by
  apply (integrable_const ((C:ℝ)*(Real.sqrt (n:ℝ)*‖w‖)^2)).mono'
    (hZ.mul ((measurable_uncurry_nativeAnisotropicFiniteDirectionalMean D s g w).of_uncurry_left.pow_const 2)).aestronglyMeasurable
  exact .of_forall fun sample=>by
    change ‖Z sample*(nativeAnisotropicFiniteDirectionalMean D s g w r sample)^2‖≤_
    rw [norm_mul,norm_pow]
    exact mul_le_mul (hC sample) (pow_le_pow_left₀ (norm_nonneg _)
      (norm_nativeAnisotropicFiniteDirectionalMean_le D s g w r sample) 2) (by positivity) C.coe_nonneg

theorem continuous_nativeFiniteMeanSquareExpectation (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Continuous (nativeFiniteMeanSquareExpectation D s g w Z) := by
  apply continuous_of_dominated (bound:=fun _ : VectorDisorderBrownianSample n=>
    (C:ℝ)*(Real.sqrt (n:ℝ)*‖w‖)^2)
  · intro r
    exact (integrable_nativeFinite_weighted_square D s g w Z hZ C hC r.toNNReal).aestronglyMeasurable
  · intro r
    exact .of_forall fun sample=>by
      rw [norm_mul,norm_pow]
      exact mul_le_mul (hC sample) (pow_le_pow_left₀ (norm_nonneg _)
        (norm_nativeAnisotropicFiniteDirectionalMean_le D s g w r.toNNReal sample) 2) (by positivity) C.coe_nonneg
  · exact integrable_const _
  · exact .of_forall fun sample=>continuous_const.mul
      (((continuous_nativeAnisotropicFiniteDirectionalMean D s g w sample).comp continuous_real_toNNReal).pow 2)

theorem continuous_nativeFiniteNoiseEnergyExpectation (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Continuous (nativeFiniteNoiseEnergyExpectation D s g w Z) := by
  apply continuous_of_dominated (bound:=fun _ : VectorDisorderBrownianSample n=>
    (C:ℝ)*nativeAnisotropicNoiseEnergyBound D w)
  · intro r
    exact (hZ.mul ((measurable_uncurry_nativeAnisotropicFiniteDirectionalNoiseEnergy D s g w).of_uncurry_left)).aestronglyMeasurable
  · intro r
    exact .of_forall fun sample=>by
      rw [norm_mul]
      have he : ‖nativeAnisotropicFiniteDirectionalNoiseEnergy D s g w r.toNNReal sample‖≤nativeAnisotropicNoiseEnergyBound D w:=by
        rw [Real.norm_eq_abs,abs_of_nonneg (nativeAnisotropicFiniteDirectionalNoiseEnergy_nonneg D s g w _ sample)]
        exact nativeAnisotropicFiniteDirectionalNoiseEnergy_le D s g w _ sample
      exact mul_le_mul (hC sample) he (norm_nonneg _) C.coe_nonneg
  · exact integrable_const _
  · exact .of_forall fun sample=>continuous_const.mul
      ((continuous_nativeAnisotropicFiniteDirectionalNoiseEnergy D s g w sample).comp continuous_real_toNNReal)

theorem nativeAnisotropic_finite_square_expectation_cropped (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (i : ℕ) (hi : i≤k+1) (a b : ℝ≥0)
    (ha : s.q i≤(a:ℝ)) (hab : a≤b) (hb : (b:ℝ)<s.q (i+1))
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n a] Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    nativeFiniteMeanSquareExpectation D s g w Z b-nativeFiniteMeanSquareExpectation D s g w Z a=
      ∫r in (a:ℝ)..(b:ℝ),nativeFiniteNoiseEnergyExpectation D s g w Z r := by
  have hZg:=hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  let source : ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>Z sample*nativeAnisotropicFiniteDirectionalNoiseEnergy D s g w r sample
  have hsm : Measurable (Function.uncurry source):=(hZg.comp measurable_snd).mul
    (measurable_uncurry_nativeAnisotropicFiniteDirectionalNoiseEnergy D s g w)
  have hbound (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : ‖source r sample‖≤
      (C:ℝ)*nativeAnisotropicNoiseEnergyBound D w:=by
    change ‖Z sample*nativeAnisotropicFiniteDirectionalNoiseEnergy D s g w r sample‖≤_
    rw [norm_mul]
    have he : ‖nativeAnisotropicFiniteDirectionalNoiseEnergy D s g w r sample‖≤nativeAnisotropicNoiseEnergyBound D w:=by
      rw [Real.norm_eq_abs,abs_of_nonneg (nativeAnisotropicFiniteDirectionalNoiseEnergy_nonneg D s g w _ sample)]
      exact nativeAnisotropicFiniteDirectionalNoiseEnergy_le D s g w _ sample
    exact mul_le_mul (hC sample) he (norm_nonneg _) C.coe_nonneg
  have hswap:=(bounded_nnreal_interval_fubini (vectorDisorderBrownianMeasure n) source hsm a b
    ((C:ℝ)*nativeAnisotropicNoiseEnergyBound D w) hbound).2
  have hreal:=nnreal_intervalIntegral_eq_real (fun r=>∫sample,source r sample∂vectorDisorderBrownianMeasure n)
    hsm.stronglyMeasurable.integral_prod_right'.measurable a b hab
  have he:=(nativeAnisotropic_finite_directional_square_cropped D s g w i hi a b ha hab hb Z hZ C hC).2
  have hia:=integrable_nativeFinite_weighted_square D s g w Z hZg C hC a
  have hib:=integrable_nativeFinite_weighted_square D s g w Z hZg C hC b
  have hfun : (fun sample=>Z sample*((nativeAnisotropicFiniteDirectionalMean D s g w b sample)^2-
      (nativeAnisotropicFiniteDirectionalMean D s g w a sample)^2))=
      fun sample=>Z sample*(nativeAnisotropicFiniteDirectionalMean D s g w b sample)^2-
        Z sample*(nativeAnisotropicFiniteDirectionalMean D s g w a sample)^2:=by funext sample;ring
  rw [hfun,integral_sub hib hia,hswap,hreal] at he
  simpa only [nativeFiniteMeanSquareExpectation,nativeFiniteNoiseEnergyExpectation,Real.toNNReal_coe,source] using he

theorem nativeAnisotropic_finite_square_expectation_closed (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (i : ℕ) (hi : i≤k+1) (a b : ℝ≥0)
    (ha : s.q i≤(a:ℝ)) (hab : a≤b) (hb : (b:ℝ)≤ s.q (i+1))
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n a] Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    nativeFiniteMeanSquareExpectation D s g w Z b-nativeFiniteMeanSquareExpectation D s g w Z a=
      ∫r in (a:ℝ)..(b:ℝ),nativeFiniteNoiseEnergyExpectation D s g w Z r := by
  rcases eq_or_lt_of_le hab with heq|hlt
  · subst b
    simp
  have hZg:=hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hFi:=continuous_nativeFiniteMeanSquareExpectation D s g w Z hZg C hC
  have hEi:=continuous_nativeFiniteNoiseEnergyExpectation D s g w Z hZg C hC
  have hh:=FRSB.closed_interval_increment_bound
    (nativeFiniteMeanSquareExpectation D s g w Z) (nativeFiniteNoiseEnergyExpectation D s g w Z)
    (fun _=>0) hFi (fun _ _=>hEi.intervalIntegrable _ _) (fun _ _=>intervalIntegrable_const)
    (show (a:ℝ)<b from hlt) (fun x y hx hxy hy=>by
      have hx0:=a.coe_nonneg.trans hx.le
      let xN : ℝ≥0:=⟨x,hx0⟩
      let yN : ℝ≥0:=⟨y,hx0.trans hxy⟩
      have hzx : Measurable[vectorBrownianFiltration n xN] Z:=
        hZ.mono ((vectorBrownianFiltration n).mono (show a≤xN from hx.le)) le_rfl
      have he:=nativeAnisotropic_finite_square_expectation_cropped D s g w i hi xN yN
        (ha.trans hx.le) (show xN≤yN from hxy) (hy.trans_le hb) Z hzx C hC
      change nativeFiniteMeanSquareExpectation D s g w Z y-nativeFiniteMeanSquareExpectation D s g w Z x=
        ∫r in x..y,nativeFiniteNoiseEnergyExpectation D s g w Z r at he
      rw [he]
      simp) le_rfl (show (a:ℝ)≤b from hab) le_rfl
  simp only [intervalIntegral.integral_zero] at hh
  exact sub_eq_zero.mp
    (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

end QuantitativeFollowup
