module
public import QuantitativeFollowup.FollowupCavityZeroCovariance
public import QuantitativeFollowup.FollowupCavitySixTermStreaming
public import QuantitativeFollowup.FollowupCavityRootNormalizerZeroResults

@[expose] public section

/-! Literal six-term finite cavity streaming on the closed interpolation
interval, including the genuine right derivative at zero row variance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency true
variable {n k : ℕ}

private theorem normalizer_replaceVariance (D:AnisotropicSpinModel n)(s:RSBScheme k)
    (a:ℝ)(i:Fin n)(b:ℝ)(hb:0<b):
    anisotropicMeasureOuterPartition (anisotropicReplaceVariance D i b) (Paper.parisiSchemeMeasure s) a=
      cavityPathNormalizer D s a i (k+2) b:=by
  rw [anisotropicMeasureOuterPartition_scheme_eq_cavityPathNormalizer _ s a i]
  rw [anisotropicReplaceVariance_variance D i i b hb,if_pos rfl]
  unfold cavityPathNormalizer
  rw [anisotropicRootEnergyMap_replaceVariance]
  have hv:anisotropicReplaceVariance (anisotropicReplaceVariance D i b) i b=anisotropicReplaceVariance D i b:=by
    simpa only [anisotropicReplaceVariance_variance D i i b hb,if_pos rfl,ite_true] using
      anisotropicReplaceVariance_self (anisotropicReplaceVariance D i b) i
  rw [hv]

private theorem normalizer_zero_root (D:AnisotropicSpinModel n)(s:RSBScheme k)
    (a:ℝ)(i:Fin n)(b:ℝ)(hq:s.q 1=0):
    cavityPathNormalizer D s a i (k+2) b=cavityPathNormalizer D s a i (k+1) b:=by
  have hz:cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s (k+1)=0:=by
    change (anisotropicEnergyMap (anisotropicReplaceVariance D i b)).comp
      (anisotropicSchemeInput (anisotropicReplaceVariance D i b) s (k+1))=0
    rw [anisotropicSchemeInput_root_zero _ s hq]
    ext x σ
    simp
  unfold cavityPathNormalizer finiteCascadeTreeGaussianNormalizer
  rw [show k+2=(k+1)+1 by omega,
    finiteStateGaussianTerminalCascade_zero_root_step _ _ _ (k+1) hz]

theorem hasDerivWithinAt_log_anisotropicCavityInterpolationPartition_zero_recorded_score
    (D:AnisotropicSpinModel n)(p:AnisotropicCouplingIndex n→Bool)(s:RSBScheme k)
    (a:ℝ)(i:Fin n){j:ℕ}(T:FiniteTerminalGenealogy j)(hJ:j=k+1)(hq:s.q 1=0)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (d alpha:ℝ)(halpha:0≤alpha)(hd:0<d-alpha):
    HasDerivWithinAt (fun v=>Real.log (anisotropicMeasureOuterPartition
      (anisotropicCavityInterpolationModel D p i d alpha v) (Paper.parisiSchemeMeasure s) a))
      (∫r,cavityInterpolationRecordScore D p s a i T alpha d r
        ∂cavityInterpolationRecordedLaw D p s a i T 0 d) (Ici (0:ℝ)) 0:=by
  have hd0:0<d:=by linarith
  let W:=fun v=>∑σ,cavityInterpolationSpinWeight D p s a i T σ v (d-alpha*v)
  have hw:HasDerivWithinAt W (∑σ,cavityInterpolationSpinResponse D p s a i T σ d alpha 0) (Ici (0:ℝ)) 0:=by
    apply HasDerivWithinAt.fun_sum
    intro σ _
    exact hasDerivWithinAt_cavityInterpolationSpinWeight_zero D p s a i T (by omega) σ d alpha halpha hd
  have hp:0<W 0:=by
    simpa only [W,mul_zero,sub_zero] using cavityInterpolationSpinWeight_sum_pos D p s a i T 0 d hd0
  have hx:=hw.log hp.ne'
  have he (v:ℝ)(hv:0<d-alpha*v):W v=anisotropicMeasureOuterPartition
      (anisotropicCavityInterpolationModel D p i d alpha v) (Paper.parisiSchemeMeasure s) a:=by
    dsimp only [W]
    simp_rw [cavityInterpolationSpinWeight_eq_actual]
    rw [sum_cavityPathSpinWeight_eq_normalizer _ s a i T _ hv]
    rw [hJ]
    exact ((normalizer_replaceVariance (anisotropicScaleRootCouplings D p v) s a i _ hv).trans
      (normalizer_zero_root _ s a i _ hq)).symm
  have hf:(fun v=>Real.log (anisotropicMeasureOuterPartition
      (anisotropicCavityInterpolationModel D p i d alpha v) (Paper.parisiSchemeMeasure s) a))=ᶠ[𝓝[Ici (0:ℝ)] 0]
      (fun v=>Real.log (W v)):=by
    have hv:∀ᶠv in 𝓝 (0:ℝ),0<d-alpha*v:=
      ((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt).eventually
        (Ioi_mem_nhds (by change 0<d-alpha*(0:ℝ);simpa only [mul_zero,sub_zero] using hd0))
    filter_upwards [hv.filter_mono nhdsWithin_le_nhds] with v hv
    rw [he v hv]
  have hi:=integral_cavityInterpolationRecordedLaw_score_mul D p s a i T (by omega) (fun _=>1) d alpha 0
    (by simpa only [mul_zero,sub_zero] using hd0)
  simp only [one_mul,mul_zero,sub_zero] at hi
  rw [hi]
  simpa only [W,mul_zero,sub_zero] using hx.congr_of_eventuallyEq_of_mem hf (by simp)

theorem integral_followupCavityPhysicalRecordScore_zero_eq_log_normalizer_derivative
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(hq:s.q 1=0)(T:FiniteTerminalGenealogy (k+2)):
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    HasDerivWithinAt (fun v=>Real.log (followupCavityRootPartition n β ρ hβ hρ (Paper.parisiSchemeMeasure s) a v))
      (∫r,followupCavityPhysicalRecordScore n β ρ hβ hρ s a T 0 r
        ∂anisotropicTrimmedRecordedTreeLaw D s a T) (Ici (0:ℝ)) 0:=by
  classical
  dsimp only
  have hb:0<followupCavityD n β ρ-followupCavityAlpha n β ρ:=by
    simpa only [followupCavityB,mul_one] using (mul_pos (sq_pos_of_pos hβ) hρ.1).trans_le
      (followupCavityB_window n β ρ 1 hρ.2 ⟨zero_le_one,le_rfl⟩).1
  have hx:=hasDerivWithinAt_log_anisotropicCavityInterpolationPartition_zero_recorded_score
    (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) (cavityIncidentRootMask n)
    s a (Fin.last n) (trimRoot T) (by omega) hq (followupCavityD n β ρ) (followupCavityAlpha n β ρ)
    (followupCavityAlpha_nonneg n β ρ hρ.2) hb
  have hm:=followupCavity_interpolation_recordedLaw_eq_actual n β ρ hβ hρ s a T 0 ⟨le_rfl,zero_le_one⟩
  dsimp only [followupCavityB] at hm
  simp only [mul_zero,sub_zero] at hm
  rw [hm] at hx
  convert! hx using 1
  simp only [followupCavityPhysicalRecordScore,followupCavityB,mul_zero,sub_zero]

theorem integral_followupCavityPhysicalRecordScore_zero_normalizer
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(has:a ≤ s.m 1)(hq:s.q 1=0)
    (T:FiniteTerminalGenealogy (k+2)):
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    (∫r,followupCavityPhysicalRecordScore n β ρ hβ hρ s a T 0 r
      ∂anisotropicTrimmedRecordedTreeLaw D s a T)=
      -a*followupCavityAlpha n β ρ/2*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a:=by
  dsimp only
  exact UniqueDiffWithinAt.eq_deriv (Ici (0:ℝ)) (uniqueDiffWithinAt_Ici (0:ℝ))
    (integral_followupCavityPhysicalRecordScore_zero_eq_log_normalizer_derivative hn β ρ hβ hρ s a hq T)
    (hasDerivWithinAt_log_followupCavityRootPartition_zero hn β ρ hβ hρ (Paper.parisiSchemeMeasure s) a ha
      (parisiSchemeMeasure_mem_scalarFloor s a ha.1 has hq))

theorem hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_zero
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(has:a ≤ s.m 1)(hq:s.q 1=0)
    (T:FiniteTerminalGenealogy (k+2))
    (F:FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ):
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    HasDerivWithinAt (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F)
      (followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation D s a T
        (followupCavityPhysicalRecordObservable n T F)) (Ici (0:ℝ)) 0:=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  obtain ⟨C,hC,hFb⟩:=exists_followupCavityPhysicalRecordObservable_bound T F
  have hd:=hasDerivWithinAt_followupCavityPhysicalExpectation_zero_recorded_covariance n β ρ hβ hρ s a T F
  dsimp only at hd
  rw [integral_followupCavityPhysicalRecordScore_mul_eq_markedFive n hn β ρ hβ hρ s a ha.1 has hq T 0
    ⟨le_rfl,zero_le_one⟩ (followupCavityPhysicalRecordObservable n T F)
      (measurable_followupCavityPhysicalRecordObservable T F) C hC hFb] at hd
  have hN:=integral_followupCavityPhysicalRecordScore_zero_normalizer hn β ρ hβ hρ s a ha has hq T
  dsimp only at hN
  rw [hN] at hd
  have hi:=followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hq T F 0 ⟨le_rfl,zero_le_one⟩
  unfold cavityMarkedSixExpectation
  rw [←hi]
  convert! hd using 1
  ring

theorem hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(has:a ≤ s.m 1)(hq:s.q 1=0)
    (T:FiniteTerminalGenealogy (k+2))
    (F:FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u:ℝ)(hu:u∈Icc (0:ℝ) 1):
    HasDerivWithinAt (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F)
      (followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a T (followupCavityPhysicalRecordObservable n T F))
        (Icc (0:ℝ) 1) u:=by
  by_cases h:u=0
  · subst u
    exact (hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_zero hn β ρ hβ hρ s a ha has hq T F).mono
      (fun _ hx=>hx.1)
  · exact (hasDerivAt_followupCavityPhysicalExpectation_six_terms hn β ρ hβ hρ s a ha has hq T F u
      ⟨lt_of_le_of_ne hu.1 (Ne.symm h),hu.2⟩).hasDerivWithinAt

end QuantitativeFollowup
