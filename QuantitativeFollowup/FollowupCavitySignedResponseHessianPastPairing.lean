module
public import QuantitativeFollowup.FollowupCavitySignedResponseConditionalPairing
public import QuantitativeFollowup.FollowupCavitySignedResponseMixedHessian
public import QuantitativeFollowup.AnisotropicProcessEnergy
public import QuantitativeFollowup.AnisotropicSpinMartingale

@[expose] public section

/-! Actual whole-past martingale pairing for the last Hessian term. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem cavitySignedResponse_future_mean_known_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p r : Paper.Overlap) (hpr : p≤r) (i : Fin n)
    (F : AnisotropicDisorderBrownianSample n→ℝ)
    (hF : StronglyMeasurable[anisotropicBrownianFiltration n (p:ℝ).toNNReal] F)
    (B : ℝ) (hB : 0≤B) (hb : ∀sample,‖F sample‖≤B) :
    (∫sample,F sample*anisotropicProcessMagnetization D μ r sample i ∂anisotropicMeasureSampleLaw D μ a)=
      ∫sample,F sample*anisotropicProcessMagnetization D μ p sample i ∂anisotropicMeasureSampleLaw D μ a := by
  let P := anisotropicMeasureSpinPathLaw D μ a
  let ambient : MeasurableSpace (AnisotropicDisorderBrownianSample n×Configuration n) := inferInstance
  let V := anisotropicSpinFiltration n p
  letI : MeasurableSpace (AnisotropicDisorderBrownianSample n×Configuration n) := ambient
  let Z := fun z : AnisotropicDisorderBrownianSample n×Configuration n=>F z.1
  let X := fun z : AnisotropicDisorderBrownianSample n×Configuration n=>anisotropicProcessMagnetization D μ r z.1 i
  have hM := anisotropic_joint_spin_mean_martingale D μ a
  have hproj := (EuclideanSpace.proj i).comp_condExp_comm (m:=V) (hM.integrable r)
  have hc : P[X|V]=ᵐ[P] fun z=>anisotropicProcessMagnetization D μ p z.1 i :=
    hproj.symm.trans ((hM.condExp_ae_eq hpr).mono fun z hz=>congrArg (fun v : Field n=>v i) hz)
  have hZ : StronglyMeasurable[V] Z := hF.comp_measurable (comap_measurable Prod.fst)
  have hZm : Measurable Z := (hZ.mono ((anisotropicSpinFiltration n).le p)).measurable
  have hvec (v : Paper.Overlap) : Measurable (anisotropicProcessMagnetization D μ v) :=
    (adapted_anisotropicProcessMagnetization D μ v).mono ((anisotropicBrownianFiltration n).le _) le_rfl
  have hXm : Measurable X := ((EuclideanSpace.proj i).measurable.comp (hvec r)).comp measurable_fst
  have hXi : Integrable X P := bounded_real_integrable _ hXm 1 fun z=>by
    change ‖anisotropicProcessSpinResponse D μ r i z.1‖≤1
    exact anisotropicProcessSpinResponse_bound D μ r i z.1
  have hZX : Integrable (fun z=>Z z*X z) P := bounded_real_integrable _ (hZm.mul hXm) B fun z=>by
    rw [norm_mul]
    have hx : ‖X z‖≤1 := anisotropicProcessSpinResponse_bound D μ r i z.1
    exact (mul_le_mul (hb z.1) hx (norm_nonneg _) hB).trans_eq (mul_one _)
  have h := integral_known_mul_condExp V ((anisotropicSpinFiltration n).le p) Z X hZ hXi hZX
  rw [integral_congr_ae (hc.mono fun z hz=>congrArg (fun v : ℝ=>Z z*v) hz)] at h
  dsimp only [Z,X] at h
  have hFp : Measurable F := (hF.mono ((anisotropicBrownianFiltration n).le _)).measurable
  have hm (v : Paper.Overlap) : Measurable (fun sample=>anisotropicProcessMagnetization D μ v sample i) :=
    measurable_anisotropicProcessSpinResponse D μ v i
  have hFpM (v : Paper.Overlap) : Measurable (fun sample=>F sample*anisotropicProcessMagnetization D μ v sample i) :=
    hFp.mul (hm v)
  change (∫z,F z.1*anisotropicProcessMagnetization D μ p z.1 i ∂anisotropicMeasureSpinPathLaw D μ a)=
    (∫z,F z.1*anisotropicProcessMagnetization D μ r z.1 i ∂anisotropicMeasureSpinPathLaw D μ a) at h
  rw [integral_anisotropicMeasureSpinPathLaw_sample D μ a
    (fun sample=>F sample*anisotropicProcessMagnetization D μ p sample i) (hFpM p),
    integral_anisotropicMeasureSpinPathLaw_sample D μ a
    (fun sample=>F sample*anisotropicProcessMagnetization D μ r sample i) (hFpM r)] at h
  exact h.symm

def cavitySignedResponseHessianMeanCoordinate (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) (i : Fin n)
    (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  cavitySignedResponseFieldHessian D μ p (anisotropicProcessParameter D μ p sample)
    (EuclideanSpace.single i 1) (anisotropicProcessMagnetization D μ p sample)

theorem adapted_cavitySignedResponseHessianMeanCoordinate (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) (i : Fin n) :
    Measurable[anisotropicBrownianFiltration n (p:ℝ).toNNReal]
      (cavitySignedResponseHessianMeanCoordinate D μ p i) := by
  have hmap : Measurable[anisotropicBrownianFiltration n (p:ℝ).toNNReal]
      (fun sample=>(p,anisotropicProcessParameter D μ p sample)) :=
    measurable_const.prodMk (adapted_anisotropicProcessParameter D μ p)
  have hT := (continuous_anisotropicMeasureTailSecondDifferential_joint D μ).measurable.comp hmap
  have hM := (anisotropicFieldInjection n).measurable.comp (adapted_anisotropicProcessMagnetization D μ p)
  have hT1 := ((ContinuousLinearMap.apply ℝ (AnisotropicParameter n→L[ℝ]ℝ))
    (anisotropicFieldInjection n (EuclideanSpace.single i 1))).measurable.comp hT
  have hev : Continuous (fun z : (AnisotropicParameter n→L[ℝ]ℝ)×AnisotropicParameter n=>z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have h := hev.measurable.comp (hT1.prodMk hM)
  dsimp only [Function.comp_def] at h
  exact h

def cavitySignedResponseHessianMeanCoordinateBound (D : AnisotropicSpinModel n) (i : Fin n) : ℝ :=
  ‖anisotropicEnergyMap D‖^2*‖anisotropicFieldInjection n (EuclideanSpace.single i 1)‖*
    (‖anisotropicFieldInjection n‖*Real.sqrt (n:ℝ))

theorem norm_cavitySignedResponseHessianMeanCoordinate_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) (i : Fin n)
    (sample : AnisotropicDisorderBrownianSample n) :
    ‖cavitySignedResponseHessianMeanCoordinate D μ p i sample‖≤
      cavitySignedResponseHessianMeanCoordinateBound D i := by
  let T := fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ p)) (anisotropicProcessParameter D μ p sample)
  let v := anisotropicFieldInjection n (EuclideanSpace.single i 1)
  let w := anisotropicFieldInjection n (anisotropicProcessMagnetization D μ p sample)
  have hv : ‖T v‖≤‖anisotropicEnergyMap D‖^2*‖v‖ :=
    (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (norm_anisotropicMeasureTailSecondDifferential_le D μ p _) (norm_nonneg _))
  have hw : ‖w‖≤‖anisotropicFieldInjection n‖*Real.sqrt (n:ℝ) :=
    ((anisotropicFieldInjection n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_anisotropicMeasureTailMagnetization_le D μ p _) (norm_nonneg _))
  exact ((T v).le_opNorm w).trans (mul_le_mul hv hw (norm_nonneg _) (by positivity))

theorem cavitySignedResponseMixedHessian_expand (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r p : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    cavitySignedResponseMixedHessian D μ r p sample=
      ∑i : Fin n,cavitySignedResponseHessianMeanCoordinate D μ p i sample*
        anisotropicProcessMagnetization D μ r sample i := by
  let I := anisotropicFieldInjection n
  let m := anisotropicProcessMagnetization D μ r sample
  have hw : I m=∑i : Fin n,m i • I (EuclideanSpace.single i 1) := by
    simp_rw [←map_smul]
    rw [←map_sum]
    congr 1
    ext i
    simp [EuclideanSpace.single_apply,Pi.single_apply]
  unfold cavitySignedResponseMixedHessian cavitySignedResponseFieldHessian
  rw [hw,map_sum]
  simp only [ContinuousLinearMap.sum_apply,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change m i*cavitySignedResponseHessianMeanCoordinate D μ p i sample=_
  ring

theorem cavitySignedResponseMixedHessianMoment_future_eq (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p r : Paper.Overlap) (hpr : p≤r) :
    cavitySignedResponseMixedHessianMoment D μ a r p=cavitySignedResponseMixedHessianMoment D μ a p p := by
  unfold cavitySignedResponseMixedHessianMoment
  congr 1
  simp_rw [cavitySignedResponseMixedHessian_expand]
  have hi (v : Paper.Overlap) (i : Fin n) : Integrable
      (fun sample=>cavitySignedResponseHessianMeanCoordinate D μ p i sample*
        anisotropicProcessMagnetization D μ v sample i) (anisotropicMeasureSampleLaw D μ a) := by
    have hF := (adapted_cavitySignedResponseHessianMeanCoordinate D μ p i).mono
      ((anisotropicBrownianFiltration n).le _) le_rfl
    have hv : Measurable (anisotropicProcessMagnetization D μ v) :=
      (adapted_anisotropicProcessMagnetization D μ v).mono ((anisotropicBrownianFiltration n).le _) le_rfl
    have hM := (EuclideanSpace.proj i).measurable.comp hv
    apply bounded_real_integrable _ (hF.mul hM) (cavitySignedResponseHessianMeanCoordinateBound D i)
    intro sample
    change ‖cavitySignedResponseHessianMeanCoordinate D μ p i sample*
      anisotropicProcessMagnetization D μ v sample i‖≤_
    rw [norm_mul]
    have hb : 0≤cavitySignedResponseHessianMeanCoordinateBound D i := by unfold cavitySignedResponseHessianMeanCoordinateBound;positivity
    exact (mul_le_mul (norm_cavitySignedResponseHessianMeanCoordinate_le D μ p i sample)
      (show ‖anisotropicProcessMagnetization D μ v sample i‖≤1 from by
        exact anisotropicProcessSpinResponse_bound D μ v i sample)
      (norm_nonneg _) hb).trans_eq (mul_one _)
  rw [integral_finset_sum _ (fun i _=>hi r i),integral_finset_sum _ (fun i _=>hi p i)]
  apply Finset.sum_congr rfl
  intro i _
  exact cavitySignedResponse_future_mean_known_pairing D μ a p r hpr i _
    (adapted_cavitySignedResponseHessianMeanCoordinate D μ p i).stronglyMeasurable _
    (by unfold cavitySignedResponseHessianMeanCoordinateBound;positivity)
    (norm_cavitySignedResponseHessianMeanCoordinate_le D μ p i)

end QuantitativeFollowup
