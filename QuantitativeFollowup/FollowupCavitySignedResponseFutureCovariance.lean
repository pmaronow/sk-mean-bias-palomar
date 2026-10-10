module
public import QuantitativeFollowup.FollowupCavitySignedResponseConditionalResidual
public import QuantitativeFollowup.FollowupCavitySignedResponseMeanResidual

@[expose] public section

/-! Actual conditional total covariance, contracted against the retained
earlier magnetization. No reaction equation is used as a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128

def cavitySignedResponseFutureCovarianceEnergy (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  anisotropicTailCovarianceQuadratic D μ l (anisotropicProcessParameter D μ l sample)
    (anisotropicProcessMagnetization D μ r sample)

theorem measurable_cavitySignedResponseFutureCovarianceEnergy (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap) :
    Measurable (cavitySignedResponseFutureCovarianceEnergy D μ r l) := by
  have hlmap : Measurable (fun sample : AnisotropicDisorderBrownianSample n => (l,sample)) :=
    measurable_const.prodMk measurable_id
  have hrmap : Measurable (fun sample : AnisotropicDisorderBrownianSample n => (r,sample)) :=
    measurable_const.prodMk measurable_id
  have hP := (measurable_uncurry_anisotropicProcessParameter D μ).comp hlmap
  have hM := (measurable_uncurry_anisotropicProcessMagnetization D μ).comp hrmap
  have hm : Measurable (fun sample : AnisotropicDisorderBrownianSample n =>
      ((l,anisotropicProcessParameter D μ l sample),anisotropicProcessMagnetization D μ r sample)) :=
    (measurable_const.prodMk hP).prodMk hM
  have h := (continuous_anisotropicTailCovarianceQuadratic_joint D μ).measurable.comp hm
  dsimp only [Function.comp_def] at h
  exact h

theorem norm_cavitySignedResponseFutureCovarianceEnergy_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    ‖cavitySignedResponseFutureCovarianceEnergy D μ r l sample‖≤(n:ℝ)^2 := by
  have h := anisotropicTailCovarianceQuadratic_bounds D μ l
    (anisotropicProcessParameter D μ l sample) (anisotropicProcessMagnetization D μ r sample)
  rw [cavitySignedResponseFutureCovarianceEnergy,Real.norm_of_nonneg h.1]
  exact h.2.trans ((mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_anisotropicMeasureTailMagnetization_le D μ r _) 2)
    (Nat.cast_nonneg n)).trans_eq (by rw [Real.sq_sqrt (Nat.cast_nonneg n)];ring))

theorem cavitySignedResponseFutureCovarianceEnergy_condVar (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r l : Paper.Overlap) (hrl : r≤l) :
    condVar (anisotropicSpinPast n (l:ℝ).toNNReal)
      (cavitySignedResponseTerminalResidual D μ r) (anisotropicMeasureSpinPathLaw D μ a) =ᵐ[
        anisotropicMeasureSpinPathLaw D μ a]
      fun p => cavitySignedResponseFutureCovarianceEnergy D μ r l p.1/(n:ℝ)^2 := by
  let P := anisotropicMeasureSpinPathLaw D μ a
  let ambient : MeasurableSpace (AnisotropicDisorderBrownianSample n×Configuration n) := inferInstance
  let V := anisotropicSpinPast n (l:ℝ).toNNReal
  letI : MeasurableSpace (AnisotropicDisorderBrownianSample n×Configuration n) := ambient
  let M := fun i : Fin n => fun p : AnisotropicDisorderBrownianSample n×Configuration n =>
    anisotropicProcessSpinResponse D μ r i p.1
  let b := fun i : Fin n => fun p : AnisotropicDisorderBrownianSample n×Configuration n => M i p/(n:ℝ)
  let X := fun i : Fin n => fun p : AnisotropicDisorderBrownianSample n×Configuration n => Paper.spinSign (p.2 i)
  let W := fun p => ∑i : Fin n,b i p*X i p
  let d := fun p => (∑i : Fin n,M i p*M i p)/(n:ℝ)
  have hM (i : Fin n) : StronglyMeasurable[V] (M i) :=
    ((adapted_anisotropicProcessSpinResponse D μ r i).mono
      ((anisotropicBrownianFiltration n).mono (Real.toNNReal_mono hrl)) le_rfl).stronglyMeasurable.comp_measurable
        (comap_measurable Prod.fst)
  have hb (i : Fin n) : StronglyMeasurable[V] (b i) := by
    simpa only [b,div_eq_mul_inv] using (hM i).mul_const ((n:ℝ)⁻¹)
  have hX (i : Fin n) : Measurable[ambient] (X i) :=
    (measurable_of_finite (fun σ : Configuration n => Paper.spinSign (σ i))).comp measurable_snd
  have hB (i : Fin n) (p) : ‖b i p‖≤(n:ℝ)⁻¹ := by
    dsimp only [b]
    rw [norm_div,Real.norm_of_nonneg (Nat.cast_nonneg n)]
    exact (div_le_div_of_nonneg_right (anisotropicProcessSpinResponse_bound D μ r i p.1)
      (Nat.cast_nonneg n)).trans_eq (by rw [one_div])
  have hXB (i : Fin n) (p) : ‖X i p‖≤1 := by simp only [X,Real.norm_eq_abs,Paper.abs_spinSign,le_refl]
  have hWm : Measurable W := Finset.measurable_sum _ (fun i _=>
    ((hb i).mono (anisotropicSpinPast_le n _)).measurable.mul (hX i))
  have hWb (p) : ‖W p‖≤(n:ℝ)*(n:ℝ)⁻¹ := by
    calc
      _≤∑i : Fin n,‖b i p*X i p‖ := norm_sum_le _ _
      _≤∑_i : Fin n,(n:ℝ)⁻¹ := Finset.sum_le_sum fun i _=>by
        rw [norm_mul]
        simpa only [mul_one] using mul_le_mul (hB i p) (hXB i p) (norm_nonneg _) (inv_nonneg.mpr (Nat.cast_nonneg n))
      _=_ := by simp
  have hWi : Integrable W P := bounded_real_integrable W hWm _ hWb
  have hd : StronglyMeasurable[V] d := by
    have hh := Finset.stronglyMeasurable_sum Finset.univ (fun i _=>(hM i).mul (hM i))
    simpa only [d,div_eq_mul_inv,Finset.sum_apply,Pi.mul_apply] using hh.mul_const ((n:ℝ)⁻¹)
  have hdb (p) : ‖d p‖≤1 := by
    have he : d p=anisotropicSelectedMeanSquare Finset.univ (anisotropicProcessMagnetization D μ r p.1) := by
      simp only [d,M,anisotropicSelectedMeanSquare,Finset.card_univ,Fintype.card_fin,←pow_two]
      rfl
    rw [he]
    exact anisotropicSelectedMeanSquare_bound _ _ (fun i=>anisotropicMeasureTailMagnetization_component_bound D μ r _ i)
  have hdi : Integrable d P := bounded_real_integrable d ((hd.mono (anisotropicSpinPast_le n _)).measurable) 1 hdb
  have he : cavitySignedResponseTerminalResidual D μ r=W-d := by
    funext p
    simp only [cavitySignedResponseTerminalResidual,cavitySignedResponseResidualCoordinate,W,d,b,M,X,
      div_mul_eq_mul_div,Finset.sum_div,mul_sub,Finset.sum_sub_distrib,sub_div,Pi.sub_apply]
  rw [he]
  have hc := condVar_sub_known V (anisotropicSpinPast_le n _) W d hWi hdi hd
  have hlin := condVar_bounded_random_linear (P:=P) V (anisotropicSpinPast_le n _) b X hb hX
    ((n:ℝ)⁻¹) (inv_nonneg.mpr (Nat.cast_nonneg n)) hB hXB
  have hp := ae_all_iff.2 (fun ij : Fin n×Fin n => anisotropicProcessSpinCovariance_eq_conditional D μ a l ij.1 ij.2)
  filter_upwards [hc,hlin,hp] with p hcp hlp hall
  rw [hcp,hlp]
  change (∑i : Fin n,∑j : Fin n,(b i p*b j p)*(P[(fun z=>X i z*X j z)|V] p-
    P[X i|V] p*P[X j|V] p))=cavitySignedResponseFutureCovarianceEnergy D μ r l p.1/(n:ℝ)^2
  simp_rw [show ∀i j,(P[(fun z=>X i z*X j z)|V] p-P[X i|V] p*P[X j|V] p)=
      anisotropicProcessSpinCovariance D μ l p.1 i j from fun i j=>hall (i,j)]
  unfold cavitySignedResponseFutureCovarianceEnergy anisotropicTailCovarianceQuadratic
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [b,M,anisotropicProcessSpinCovariance,anisotropicProcessSpinResponse,anisotropicProcessMagnetization]
  ring

theorem cavitySignedResponse_future_covariance_moment_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r l : Paper.Overlap) (hrl : r≤l) :
    (∫sample,cavitySignedResponseFutureCovarianceEnergy D μ r l sample
      ∂anisotropicMeasureSampleLaw D μ a)/(n:ℝ)^2 ≤
      cavitySignedResponseCovarianceMoment D μ a Finset.univ r := by
  let P := anisotropicMeasureSpinPathLaw D μ a
  have hx := memLp_two_cavitySignedResponseTerminalResidual D μ a r
  have h := integral_condVar_le_variance (anisotropicSpinPast n (l:ℝ).toNNReal)
    (anisotropicSpinPast_le n _) (cavitySignedResponseTerminalResidual D μ r) hx
  have he := integral_congr_ae (cavitySignedResponseFutureCovarianceEnergy_condVar D μ a r l hrl)
  rw [he] at h
  rw [integral_anisotropicMeasureSpinPathLaw_sample D μ a _
    ((measurable_cavitySignedResponseFutureCovarianceEnergy D μ r l).div_const _),integral_div] at h
  rw [variance_eq_sub hx] at h
  simp only [Pi.pow_apply] at h
  rw [cavitySignedResponseTerminalResidual_centered,cavitySignedResponseTerminalResidual_second_moment,
    zero_pow (by decide : 2≠0),sub_zero] at h
  exact h

end QuantitativeFollowup
