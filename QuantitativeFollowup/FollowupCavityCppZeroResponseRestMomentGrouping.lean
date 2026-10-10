module
public import QuantitativeFollowup.FollowupCavityRestTraceColumns
public import QuantitativeFollowup.FollowupCavitySignedResponseSelfOverlap

@[expose] public section

/-! Exact native rest moments in the finite response grouping. Terminal and
two-time normalized pairings split into the true covariance column and the
literal centered residual; no conditional moment identity is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

private theorem measurable_rest_self (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    Measurable (cavitySignedResponseSelfOverlap D μ p) :=by
  have hm : Measurable (fun z : AnisotropicDisorderBrownianSample n => (p,z)) :=
    measurable_const.prodMk measurable_id
  simpa only [Function.comp_def,Function.uncurry_def] using
    (measurable_joint_cavitySignedResponseSelfOverlap D μ).comp hm

private theorem measurable_rest_centered (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p) :=by
  have hm : Measurable (fun z : AnisotropicDisorderBrownianSample n => (p,z)) :=
    measurable_const.prodMk measurable_id
  simpa only [Function.comp_def,Function.uncurry_def] using
    (measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp hm

private theorem measurable_rest_symmetric (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap) :
    Measurable (cavitySignedResponseSymmetricMeanResidual D μ r l) :=by
  have hm : Measurable (fun z : AnisotropicDisorderBrownianSample n => ((r,l),z)) :=
    measurable_const.prodMk measurable_id
  simpa only [Function.comp_def] using
    (measurable_joint_cavitySignedResponseSymmetricMeanResidual D μ).comp hm

private theorem integrable_bounded_pairing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F C : Ω → ℝ)
    (hF : Measurable F) (hC : Measurable C)
    (B D : ℝ) (hB : 0≤B) (hnF : ∀z,‖F z‖≤B) (hnC : ∀z,‖C z‖≤D) :
    Integrable (fun z=>F z*C z) P :=by
  apply bounded_real_integrable (P:=P) (fun z=>F z*C z)
    (by simpa only [Pi.mul_def] using hF.mul hC) (B*D)
  intro z
  rw [norm_mul]
  exact mul_le_mul (hnF z) (hnC z) (norm_nonneg _) hB

private theorem integral_sum_pairing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (R S C : Ω → ℝ)
    (hR : Integrable (fun z => R z * C z) P)
    (hS : Integrable (fun z => S z * C z) P) :
    (∫z, (R z + S z) * C z ∂P) =
      (∫z, S z * C z ∂P) + ∫z, R z * C z ∂P := by
  simp_rw [add_mul]
  rw [integral_add hR hS, add_comm]

private theorem integral_mul_centered {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F G : Ω→ℝ)
    (hF : MemLp F 2 P) (hG : MemLp G 2 P) :
    (∫p,F p*(G p-∫z,G z ∂P) ∂P)=
      ∫p,(F p-∫z,F z ∂P)*(G p-∫z,G z ∂P) ∂P :=by
  have hiG:=(hG.sub (memLp_const (∫z,G z ∂P))).integrable (by norm_num)
  have hz:(∫p,G p-∫z,G z ∂P ∂P)=0 :=by
    rw [integral_sub (hG.integrable (by norm_num)) (integrable_const _)]
    simp only [integral_const,probReal_univ,one_smul,sub_self]
  symm
  simp_rw [sub_mul]
  have hiFG : Integrable (fun p=>F p*(G p-∫z,G z ∂P)) P :=
    hF.integrable_mul (hG.sub (memLp_const _))
  have hiCF : Integrable (fun p=>(∫z,F z ∂P)*(G p-∫z,G z ∂P)) P :=hiG.const_mul _
  rw [integral_sub hiFG hiCF,integral_const_mul,hz,mul_zero,sub_zero]

private theorem rest_self_memLp_two (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) :
    MemLp (cavitySignedResponseSelfOverlap D μ r) 2 (anisotropicMeasureSampleLaw D μ a) :=by
  exact MemLp.of_bound (measurable_rest_self D μ r).aestronglyMeasurable 1
      (.of_forall (norm_cavitySignedResponseSelfOverlap_le D μ r))

theorem cavityRestCovarianceColumn_eq_self_centered_moment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p r : Paper.Overlap) :
    cavityRestCovarianceColumn D μ a p r=
      ∫sample,cavitySignedResponseSelfOverlap D μ r sample*
        cavitySignedResponseCenteredSelfOverlap D μ a p sample ∂anisotropicMeasureSampleLaw D μ a :=by
  simp only [cavitySignedResponseCenteredSelfOverlap]
  rw [integral_mul_centered _ _ _ (rest_self_memLp_two D μ a r) (rest_self_memLp_two D μ a p),
    cavityRestCovarianceColumn_apply]
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    change (cavityRestSelfOverlap D μ p sample-cavityRestOverlapMean D μ a p)*
      (cavityRestSelfOverlap D μ r sample-cavityRestOverlapMean D μ a r)=_
    rw [cavityRestOverlapMean_apply,cavityRestOverlapMean_apply]
    exact mul_comm _ _

def cavityRestTerminalMeanPairing (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (r : Paper.Overlap) (z : AnisotropicDisorderBrownianSample n×Configuration n) : ℝ :=
  (∑i : Fin n,Paper.spinSign (z.2 i)*anisotropicProcessSpinResponse D μ r i z.1)/(n:ℝ)

def cavityRestTwoTimeMeanPairing (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (r l : Paper.Overlap) (z : AnisotropicDisorderBrownianSample n) : ℝ :=
  (∑i : Fin n,anisotropicProcessSpinResponse D μ r i z*
    anisotropicProcessSpinResponse D μ l i z)/(n:ℝ)

theorem measurable_cavityRestTerminalMeanPairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r : Paper.Overlap) :
    Measurable (cavityRestTerminalMeanPairing D μ r) :=by
  unfold cavityRestTerminalMeanPairing
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_of_finite (fun τ : Configuration n=>Paper.spinSign (τ i))).comp
    measurable_snd).mul ((measurable_anisotropicProcessSpinResponse D μ r i).comp measurable_fst)

theorem measurable_cavityRestTwoTimeMeanPairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap) :
    Measurable (cavityRestTwoTimeMeanPairing D μ r l) :=by
  unfold cavityRestTwoTimeMeanPairing
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  exact (measurable_anisotropicProcessSpinResponse D μ r i).mul
    (measurable_anisotropicProcessSpinResponse D μ l i)

private theorem normalized_pairing_split {I : Type*} [Fintype I]
    (v w : I→ℝ) (c : ℝ) :
    (∑i,w i*v i)/c=(∑i,v i*(w i-v i))/c+(∑i,(v i)^2)/c :=by
  have he : (∑i,w i*v i)=∑i,v i*w i :=
    Finset.sum_congr rfl (fun i _=>mul_comm _ _)
  simp_rw [mul_sub,pow_two]
  rw [Finset.sum_sub_distrib,he]
  ring

theorem cavityRestTerminalMeanPairing_eq_residual_add_self (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r : Paper.Overlap)
    (z : AnisotropicDisorderBrownianSample n×Configuration n) :
    cavityRestTerminalMeanPairing D μ r z=
      cavitySignedResponseTerminalResidual D μ r z+cavitySignedResponseSelfOverlap D μ r z.1 :=by
  simp only [cavityRestTerminalMeanPairing,cavitySignedResponseTerminalResidual,
    cavitySignedResponseResidualCoordinate,cavitySignedResponseSelfOverlap,
    anisotropicSelectedMeanSquare,Finset.card_univ,Fintype.card_fin,
    anisotropicProcessSpinResponse,Finset.mem_univ,if_true]
  exact normalized_pairing_split _ _ _

theorem cavityRestTwoTimeMeanPairing_eq_residual_add_self (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap)
    (z : AnisotropicDisorderBrownianSample n) :
    cavityRestTwoTimeMeanPairing D μ r l z=
      cavitySignedResponseSymmetricMeanResidual D μ r l z+
        cavitySignedResponseSelfOverlap D μ (min r l) z :=by
  by_cases h:r≤l
  · simp only [cavityRestTwoTimeMeanPairing,cavitySignedResponseSymmetricMeanResidual,
      min_eq_left h,max_eq_right h,cavitySignedResponseMeanResidual,
      cavitySignedResponseSelfOverlap,anisotropicSelectedMeanSquare,
      Finset.card_univ,Fintype.card_fin,Finset.mem_univ,if_true]
    simpa only [mul_comm,anisotropicProcessSpinResponse] using (normalized_pairing_split
      (fun i=>anisotropicProcessSpinResponse D μ r i z)
      (fun i=>anisotropicProcessSpinResponse D μ l i z) (n:ℝ))
  · have h':l≤r:=le_of_not_ge h
    simp only [cavityRestTwoTimeMeanPairing,cavitySignedResponseSymmetricMeanResidual,
      min_eq_right h',max_eq_left h',cavitySignedResponseMeanResidual,
      cavitySignedResponseSelfOverlap,anisotropicSelectedMeanSquare,
      Finset.card_univ,Fintype.card_fin,Finset.mem_univ,if_true]
    exact normalized_pairing_split _ _ _

theorem norm_cavityRestTerminalMeanPairing_le_three (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r : Paper.Overlap)
    (z : AnisotropicDisorderBrownianSample n×Configuration n) :
    ‖cavityRestTerminalMeanPairing D μ r z‖≤3 :=by
  rw [cavityRestTerminalMeanPairing_eq_residual_add_self]
  exact (norm_add_le _ _).trans ((add_le_add
    (norm_cavitySignedResponseTerminalResidual_le D μ r z)
    (norm_cavitySignedResponseSelfOverlap_le D μ r z.1)).trans_eq (by norm_num))

theorem norm_cavityRestTwoTimeMeanPairing_le_three (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap)
    (z : AnisotropicDisorderBrownianSample n) :
    ‖cavityRestTwoTimeMeanPairing D μ r l z‖≤3 :=by
  rw [cavityRestTwoTimeMeanPairing_eq_residual_add_self]
  exact (norm_add_le _ _).trans ((add_le_add
    (norm_cavitySignedResponseMeanResidual_le D μ (min r l) (max r l) z)
    (norm_cavitySignedResponseSelfOverlap_le D μ (min r l) z)).trans_eq (by norm_num))

theorem cavityRestTerminalMeanPairing_centered_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p : Paper.Overlap) :
    (∫z,cavityRestTerminalMeanPairing D μ r z*cavitySignedResponseCenteredSelfOverlap D μ a p z.1
      ∂anisotropicMeasureSpinPathLaw D μ a)=
      cavityRestCovarianceColumn D μ a p r+
        ∫z,cavitySignedResponseTerminalResidual D μ r z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z.1 ∂anisotropicMeasureSpinPathLaw D μ a :=by
  let P:=anisotropicMeasureSpinPathLaw D μ a
  have hC : Measurable (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
      cavitySignedResponseCenteredSelfOverlap D μ a p z.1) :=
    (measurable_rest_centered D μ a p).comp measurable_fst
  have hS : Measurable (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
      cavitySignedResponseSelfOverlap D μ r z.1) :=
    (measurable_rest_self D μ r).comp measurable_fst
  have hiRC : Integrable (fun z=>cavitySignedResponseTerminalResidual D μ r z*
      cavitySignedResponseCenteredSelfOverlap D μ a p z.1) P :=
    integrable_bounded_pairing P _ _ (measurable_cavitySignedResponseTerminalResidual D μ r)
      hC 2 2 (by norm_num) (norm_cavitySignedResponseTerminalResidual_le D μ r)
      (fun z=>norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p z.1)
  have hiSC : Integrable (fun z=>cavitySignedResponseSelfOverlap D μ r z.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p z.1) P :=
    integrable_bounded_pairing P _ _ hS hC 1 2 (by norm_num)
      (fun z=>norm_cavitySignedResponseSelfOverlap_le D μ r z.1)
      (fun z=>norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p z.1)
  let F : AnisotropicDisorderBrownianSample n → ℝ := fun sample =>
    cavitySignedResponseSelfOverlap D μ r sample *
      cavitySignedResponseCenteredSelfOverlap D μ a p sample
  have hF : Measurable F :=
    (measurable_rest_self D μ r).mul (measurable_rest_centered D μ a p)
  have he1 : (∫z,F z.1 ∂P) = ∫sample,F sample ∂anisotropicMeasureSampleLaw D μ a := by
    change (∫z,F z.1 ∂anisotropicMeasureSpinPathLaw D μ a) = _
    exact integral_anisotropicMeasureSpinPathLaw_sample D μ a F hF
  have he2 : (∫sample,F sample ∂anisotropicMeasureSampleLaw D μ a) =
      cavityRestCovarianceColumn D μ a p r :=
    (cavityRestCovarianceColumn_eq_self_centered_moment D μ a p r).symm
  have he : (∫z,cavitySignedResponseSelfOverlap D μ r z.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p z.1 ∂P)=
      cavityRestCovarianceColumn D μ a p r := he1.trans he2
  calc
    _ = ∫z,(cavitySignedResponseTerminalResidual D μ r z +
        cavitySignedResponseSelfOverlap D μ r z.1)*
        cavitySignedResponseCenteredSelfOverlap D μ a p z.1 ∂P := by
      apply integral_congr_ae
      exact .of_forall fun z => congrArg
        (fun x : ℝ => x * cavitySignedResponseCenteredSelfOverlap D μ a p z.1)
        (cavityRestTerminalMeanPairing_eq_residual_add_self D μ r z)
    _ = (∫z,cavitySignedResponseSelfOverlap D μ r z.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p z.1 ∂P) +
        ∫z,cavitySignedResponseTerminalResidual D μ r z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z.1 ∂P :=
      integral_sum_pairing P _ _ _ hiRC hiSC
    _ = _ := congrArg (fun x : ℝ => x +
      ∫z,cavitySignedResponseTerminalResidual D μ r z*
        cavitySignedResponseCenteredSelfOverlap D μ a p z.1 ∂P) he

theorem cavityRestTwoTimeMeanPairing_centered_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r l p : Paper.Overlap) :
    (∫z,cavityRestTwoTimeMeanPairing D μ r l z*cavitySignedResponseCenteredSelfOverlap D μ a p z
      ∂anisotropicMeasureSampleLaw D μ a)=
      cavityRestCovarianceColumn D μ a p (min r l)+
        ∫z,cavitySignedResponseSymmetricMeanResidual D μ r l z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z ∂anisotropicMeasureSampleLaw D μ a :=by
  have hC : Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p) :=
    measurable_rest_centered D μ a p
  have hY : Measurable (cavitySignedResponseSymmetricMeanResidual D μ r l) :=
    measurable_rest_symmetric D μ r l
  have hS : Measurable (cavitySignedResponseSelfOverlap D μ (min r l)) :=
    measurable_rest_self D μ (min r l)
  have hiYC : Integrable (fun z=>cavitySignedResponseSymmetricMeanResidual D μ r l z*
      cavitySignedResponseCenteredSelfOverlap D μ a p z) (anisotropicMeasureSampleLaw D μ a) :=
    integrable_bounded_pairing _ _ _ hY hC 2 2 (by norm_num)
      (norm_cavitySignedResponseMeanResidual_le D μ (min r l) (max r l))
      (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p)
  have hiSC : Integrable (fun z=>cavitySignedResponseSelfOverlap D μ (min r l) z*
      cavitySignedResponseCenteredSelfOverlap D μ a p z) (anisotropicMeasureSampleLaw D μ a) :=
    integrable_bounded_pairing _ _ _ hS hC 1 2 (by norm_num)
      (norm_cavitySignedResponseSelfOverlap_le D μ (min r l))
      (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p)
  have he := (cavityRestCovarianceColumn_eq_self_centered_moment D μ a p (min r l)).symm
  calc
    _ = ∫z,(cavitySignedResponseSymmetricMeanResidual D μ r l z +
        cavitySignedResponseSelfOverlap D μ (min r l) z)*
        cavitySignedResponseCenteredSelfOverlap D μ a p z ∂anisotropicMeasureSampleLaw D μ a := by
      apply integral_congr_ae
      exact .of_forall fun z => congrArg
        (fun x : ℝ => x * cavitySignedResponseCenteredSelfOverlap D μ a p z)
        (cavityRestTwoTimeMeanPairing_eq_residual_add_self D μ r l z)
    _ = (∫z,cavitySignedResponseSelfOverlap D μ (min r l) z*
        cavitySignedResponseCenteredSelfOverlap D μ a p z ∂anisotropicMeasureSampleLaw D μ a) +
        ∫z,cavitySignedResponseSymmetricMeanResidual D μ r l z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z ∂anisotropicMeasureSampleLaw D μ a :=
      integral_sum_pairing _ _ _ _ hiYC hiSC
    _ = _ := congrArg (fun x : ℝ => x +
      ∫z,cavitySignedResponseSymmetricMeanResidual D μ r l z*
        cavitySignedResponseCenteredSelfOverlap D μ a p z ∂anisotropicMeasureSampleLaw D μ a) he

end QuantitativeFollowup
