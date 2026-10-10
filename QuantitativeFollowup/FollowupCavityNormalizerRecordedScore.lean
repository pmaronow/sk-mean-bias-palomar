module
public import QuantitativeFollowup.FollowupCavityMarkedCovariance
public import QuantitativeFollowup.AnisotropicFiniteMeasureAgreement
public import QuantitativeFollowup.FollowupCavityRootNormalizerResults

@[expose] public section

/-! The retained-tree score has the actual one-leaf normalizer derivative.
The numerator integral is differentiated on the genuine fixed Gaussian
coordinates, then identified with the arbitrary-profile root partition. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
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

theorem hasDerivAt_log_anisotropicCavityInterpolationPartition_recorded_score
    (D:AnisotropicSpinModel n)(p:AnisotropicCouplingIndex n→Bool)(s:RSBScheme k)
    (a:ℝ)(i:Fin n){j:ℕ}(T:FiniteTerminalGenealogy j)(hJ:j=k+1)(hq:s.q 1=0)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (d alpha u:ℝ)(halpha:0≤alpha)(hu:0<u)(hb:0<d-alpha*u):
    HasDerivAt (fun v=>Real.log (anisotropicMeasureOuterPartition
      (anisotropicCavityInterpolationModel D p i d alpha v) (Paper.parisiSchemeMeasure s) a))
      (∫r,cavityInterpolationRecordScore D p s a i T alpha (d-alpha*u) r
        ∂cavityInterpolationRecordedLaw D p s a i T u (d-alpha*u)) u:=by
  let W:=fun v=>∑σ,cavityInterpolationSpinWeight D p s a i T σ v (d-alpha*v)
  have hw:HasDerivAt W (∑σ,cavityInterpolationSpinResponse D p s a i T σ d alpha u) u:=by
    apply HasDerivAt.fun_sum
    intro σ _
    exact hasDerivAt_cavityInterpolationSpinWeight_record_score D p s a i T (by omega) σ d alpha u halpha hu hb
  have hp:0<W u:=cavityInterpolationSpinWeight_sum_pos D p s a i T u (d-alpha*u) hb
  have hd:=hw.log hp.ne'
  have he (v:ℝ)(hv:0<d-alpha*v):W v=anisotropicMeasureOuterPartition
      (anisotropicCavityInterpolationModel D p i d alpha v) (Paper.parisiSchemeMeasure s) a:=by
    dsimp only [W]
    simp_rw [cavityInterpolationSpinWeight_eq_actual]
    rw [sum_cavityPathSpinWeight_eq_normalizer _ s a i T _ hv]
    rw [hJ]
    exact ((normalizer_replaceVariance (anisotropicScaleRootCouplings D p v) s a i _ hv).trans
      (normalizer_zero_root _ s a i _ hq)).symm
  have hf:(fun v=>Real.log (W v))=ᶠ[𝓝 u](fun v=>Real.log (anisotropicMeasureOuterPartition
      (anisotropicCavityInterpolationModel D p i d alpha v) (Paper.parisiSchemeMeasure s) a)):=by
    have hv:∀ᶠv in 𝓝 u,0<d-alpha*v:=
      ((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt).eventually (Ioi_mem_nhds hb)
    filter_upwards [hv] with v hv
    rw [he v hv]
  have hi:=integral_cavityInterpolationRecordedLaw_score_mul D p s a i T (by omega) (fun _=>1) d alpha u hb
  simp only [one_mul] at hi
  rw [hi]
  exact hd.congr_of_eventuallyEq hf.symm

theorem integral_followupCavityPhysicalRecordScore_eq_log_normalizer_derivative
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(hq:s.q 1=0)(T:FiniteTerminalGenealogy (k+2))(u:ℝ)(hu:u∈Ioc (0:ℝ) 1):
    HasDerivAt (fun v=>Real.log (followupCavityRootPartition n β ρ hβ hρ (Paper.parisiSchemeMeasure s) a v))
      (∫r,followupCavityPhysicalRecordScore n β ρ hβ hρ s a T u r
        ∂anisotropicTrimmedRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u ⟨hu.1.le,hu.2⟩) s a T) u:=by
  classical
  have hb:0<followupCavityD n β ρ-followupCavityAlpha n β ρ*u:=
    (mul_pos (sq_pos_of_pos hβ) hρ.1).trans_le (followupCavityB_window n β ρ u hρ.2 ⟨hu.1.le,hu.2⟩).1
  have hd:=hasDerivAt_log_anisotropicCavityInterpolationPartition_recorded_score
    (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) (cavityIncidentRootMask n)
    s a (Fin.last n) (trimRoot T) (by omega) hq (followupCavityD n β ρ) (followupCavityAlpha n β ρ) u
    (followupCavityAlpha_nonneg n β ρ hρ.2) hu.1 hb
  have hm:=followupCavity_interpolation_recordedLaw_eq_actual n β ρ hβ hρ s a T u ⟨hu.1.le,hu.2⟩
  dsimp only [followupCavityB] at hm
  rw [hm] at hd
  exact hd

end QuantitativeFollowup
