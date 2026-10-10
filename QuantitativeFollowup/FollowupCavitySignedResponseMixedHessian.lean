module
public import QuantitativeFollowup.FollowupCavitySignedResponseFutureCovariance
public import QuantitativePaper.ResponseScalarIntegralCauchySchwarz
public import Mathlib.Algebra.QuadraticDiscriminant

@[expose] public section

/-! Mixed genuine field-Hessian pairings. Positivity and the posterior
covariance sandwich yield Cauchy--Schwarz; conditional total covariance
then controls an earlier magnetization at every later time. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

def cavitySignedResponseFieldHessian (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (w v : Field n) : ℝ :=
  fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) P
    (anisotropicFieldInjection n w) (anisotropicFieldInjection n v)

theorem cavitySignedResponseFieldHessian_nonneg (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (w : Field n) :
    0≤cavitySignedResponseFieldHessian D μ q P w w :=
  (mul_nonneg (Paper.parisiCDF_nonneg μ q)
    (anisotropicTailCovarianceQuadratic_bounds D μ q P w).1).trans
    (anisotropicMeasureTail_covariance_bounds D μ q P w).1

theorem cavitySignedResponseFieldHessian_square_le_covariance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) (w v : Field n) :
    (cavitySignedResponseFieldHessian D μ q P w v)^2≤
      anisotropicTailCovarianceQuadratic D μ q P w*anisotropicTailCovarianceQuadratic D μ q P v := by
  let T := fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) P
  let I := anisotropicFieldInjection n
  have hs : T (I v) (I w)=T (I w) (I v) :=
    ((anisotropicMeasureTailPotential_hessian_limit D μ q).2.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _
  have hq (x : ℝ) : 0≤T (I w) (I w)*(x*x)+(2*T (I w) (I v))*x+T (I v) (I v) := by
    have h := cavitySignedResponseFieldHessian_nonneg D μ q P (x • w+v)
    change 0≤T (I (x • w+v)) (I (x • w+v)) at h
    simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul] at h
    rw [hs] at h
    nlinarith only [h]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have hm : (T (I w) (I v))^2≤T (I w) (I w)*T (I v) (I v) := by nlinarith only [hd]
  exact hm.trans (mul_le_mul (anisotropicMeasureTail_covariance_bounds D μ q P w).2
    (anisotropicMeasureTail_covariance_bounds D μ q P v).2
    (cavitySignedResponseFieldHessian_nonneg D μ q P v) (anisotropicTailCovarianceQuadratic_bounds D μ q P w).1)

def cavitySignedResponseMixedHessian (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (r l : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  cavitySignedResponseFieldHessian D μ l (anisotropicProcessParameter D μ l sample)
    (anisotropicProcessMagnetization D μ r sample) (anisotropicProcessMagnetization D μ l sample)

theorem measurable_cavitySignedResponseMixedHessian (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap) :
    Measurable (cavitySignedResponseMixedHessian D μ r l) := by
  have hTmap : Measurable (fun sample : AnisotropicDisorderBrownianSample n =>
      (l,anisotropicProcessParameter D μ l sample)) := measurable_const.prodMk
        ((measurable_uncurry_anisotropicProcessParameter D μ).of_uncurry_left)
  have hT := (continuous_anisotropicMeasureTailSecondDifferential_joint D μ).measurable.comp hTmap
  have hrmap : Measurable (fun sample : AnisotropicDisorderBrownianSample n => (r,sample)) :=
    measurable_const.prodMk measurable_id
  have hlmap : Measurable (fun sample : AnisotropicDisorderBrownianSample n => (l,sample)) :=
    measurable_const.prodMk measurable_id
  have hr := (anisotropicFieldInjection n).continuous.measurable.comp
    ((measurable_uncurry_anisotropicProcessMagnetization D μ).comp hrmap)
  have hl := (anisotropicFieldInjection n).continuous.measurable.comp
    ((measurable_uncurry_anisotropicProcessMagnetization D μ).comp hlmap)
  have hev : Continuous (fun z : ((AnisotropicParameter n→L[ℝ](AnisotropicParameter n→L[ℝ]ℝ))×
      AnisotropicParameter n)×AnisotropicParameter n =>z.1.1 z.1.2 z.2) :=
    (continuous_fst.fst.clm_apply continuous_fst.snd).clm_apply continuous_snd
  have h := hev.measurable.comp ((hT.prodMk hr).prodMk hl)
  dsimp only [Function.comp_def] at h
  exact h

theorem norm_cavitySignedResponseMixedHessian_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    ‖cavitySignedResponseMixedHessian D μ r l sample‖≤(n:ℝ)^2 := by
  have hh := cavitySignedResponseFieldHessian_square_le_covariance D μ l
    (anisotropicProcessParameter D μ l sample)
    (anisotropicProcessMagnetization D μ r sample) (anisotropicProcessMagnetization D μ l sample)
  have hr := norm_cavitySignedResponseFutureCovarianceEnergy_le D μ r l sample
  have hl := norm_cavitySignedResponseFutureCovarianceEnergy_le D μ l l sample
  have hrl := (anisotropicTailCovarianceQuadratic_bounds D μ l (anisotropicProcessParameter D μ l sample)
    (anisotropicProcessMagnetization D μ r sample)).1
  have hll := (anisotropicTailCovarianceQuadratic_bounds D μ l (anisotropicProcessParameter D μ l sample)
    (anisotropicProcessMagnetization D μ l sample)).1
  change 0≤cavitySignedResponseFutureCovarianceEnergy D μ r l sample at hrl
  change 0≤cavitySignedResponseFutureCovarianceEnergy D μ l l sample at hll
  rw [Real.norm_of_nonneg hrl] at hr
  rw [Real.norm_of_nonneg hll] at hl
  have hprod := mul_le_mul hr hl hll (sq_nonneg (n:ℝ))
  change (cavitySignedResponseMixedHessian D μ r l sample)^2≤
    cavitySignedResponseFutureCovarianceEnergy D μ r l sample*cavitySignedResponseFutureCovarianceEnergy D μ l l sample at hh
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (cavitySignedResponseMixedHessian D μ r l sample),
    abs_nonneg (cavitySignedResponseMixedHessian D μ r l sample)]

def cavitySignedResponseMixedHessianMoment (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (r l : Paper.Overlap) : ℝ :=
  (∫sample,cavitySignedResponseMixedHessian D μ r l sample ∂anisotropicMeasureSampleLaw D μ a)/(n:ℝ)^2

theorem cavitySignedResponseMixedHessianMoment_square_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r l : Paper.Overlap) (hrl : r≤l) :
    (cavitySignedResponseMixedHessianMoment D μ a r l)^2≤
      cavitySignedResponseCovarianceMoment D μ a Finset.univ r*
        cavitySignedResponseCovarianceMoment D μ a Finset.univ l := by
  let P := anisotropicMeasureSampleLaw D μ a
  let e := cavitySignedResponseFutureCovarianceEnergy D μ r l
  let f := cavitySignedResponseMixedHessian D μ r l
  let x := cavitySignedResponseFutureCovarianceEnergy D μ l l
  have he : Integrable e P := bounded_real_integrable e (measurable_cavitySignedResponseFutureCovarianceEnergy D μ r l)
    _ (norm_cavitySignedResponseFutureCovarianceEnergy_le D μ r l)
  have hf : Integrable f P := bounded_real_integrable f (measurable_cavitySignedResponseMixedHessian D μ r l)
    _ (norm_cavitySignedResponseMixedHessian_le D μ r l)
  have hx : Integrable x P := bounded_real_integrable x (measurable_cavitySignedResponseFutureCovarianceEnergy D μ l l)
    _ (norm_cavitySignedResponseFutureCovarianceEnergy_le D μ l l)
  have h := response_integral_scalar_cauchy_schwarz P e f x he hf hx (.of_forall fun sample =>
    ⟨(anisotropicTailCovarianceQuadratic_bounds D μ l _ _).1,
      (anisotropicTailCovarianceQuadratic_bounds D μ l _ _).1,
      cavitySignedResponseFieldHessian_square_le_covariance D μ l _ _ _⟩)
  have he0 : 0≤(∫sample,e sample ∂P) := integral_nonneg fun sample => (anisotropicTailCovarianceQuadratic_bounds D μ l _ _).1
  have hx0 : 0≤(∫sample,x sample ∂P) := integral_nonneg fun sample => (anisotropicTailCovarianceQuadratic_bounds D μ l _ _).1
  have hed := cavitySignedResponse_future_covariance_moment_le D μ a r l hrl
  have hxd : (∫sample,x sample ∂P)/(n:ℝ)^2=cavitySignedResponseCovarianceMoment D μ a Finset.univ l := by
    unfold cavitySignedResponseCovarianceMoment
    simp only [Finset.card_univ,Fintype.card_fin]
    congr 1
    apply integral_congr_ae
    exact .of_forall fun sample => by
      unfold x cavitySignedResponseFutureCovarianceEnergy anisotropicProcessCovarianceEnergy
      rw [anisotropicSelectedFieldMap_univ]
  have hn0 : 0≤(n:ℝ)^2 := sq_nonneg _
  calc
    _=(∫sample,f sample ∂P)^2/((n:ℝ)^2*(n:ℝ)^2) := by
      unfold cavitySignedResponseMixedHessianMoment
      simp only [div_pow]
      ring
    _≤((∫sample,e sample ∂P)*(∫sample,x sample ∂P))/((n:ℝ)^2*(n:ℝ)^2) :=
      div_le_div_of_nonneg_right h (mul_nonneg hn0 hn0)
    _=((∫sample,e sample ∂P)/(n:ℝ)^2)*((∫sample,x sample ∂P)/(n:ℝ)^2) := by ring
    _≤_ := by rw [hxd]; exact mul_le_mul_of_nonneg_right hed (cavitySignedResponseCovarianceMoment_nonneg D μ a _ l)

end QuantitativeFollowup
