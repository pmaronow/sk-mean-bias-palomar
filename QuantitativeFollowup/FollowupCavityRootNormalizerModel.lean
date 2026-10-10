module
public import QuantitativeFollowup.FollowupCavityRootNormalizerTransport
public import QuantitativeFollowup.FollowupCavityRootNormalizerRawDerivative

@[expose] public section

/-! The moving Gaussian coordinates are identified with the actual cavity
model. Variance response transport is proved by uniqueness of the genuine
variance derivatives, rather than by assuming diffusion-law invariance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem anisotropicReplaceVariance_scaleRootCouplings (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) (i : Fin n) (b : ℝ) :
    anisotropicReplaceVariance (anisotropicScaleRootCouplings D p u) i b=
      anisotropicScaleRootCouplings (anisotropicReplaceVariance D i b) p u := rfl

def anisotropicCavityInterpolationModel (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (i : Fin n) (d alpha u : ℝ) : AnisotropicSpinModel n :=
  anisotropicReplaceVariance (anisotropicScaleRootCouplings D p u) i (d-alpha*u)

theorem anisotropicCavityInterpolationModel_potential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : AnisotropicCouplingIndex n→Bool)
    (i : Fin n) (d alpha u : ℝ) (g : AnisotropicDisorder n) :
    anisotropicMeasurePotential (anisotropicCavityInterpolationModel D p i d alpha u) μ
        (anisotropicDisorderInjection n g)=anisotropicMovingRootPotential D μ p i d alpha u g := by
  rw [anisotropicCavityInterpolationModel,anisotropicReplaceVariance_scaleRootCouplings,
    anisotropicMeasurePotential_rootCouplingScale]
  rfl

theorem anisotropicMovingRootPartition_eq_actual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : AnisotropicCouplingIndex n→Bool)
    (i : Fin n) (d alpha u : ℝ) :
    anisotropicMovingRootPartition D μ a p i d alpha u=
      anisotropicMeasureOuterPartition (anisotropicCavityInterpolationModel D p i d alpha u) μ a := by
  unfold anisotropicMovingRootPartition anisotropicMeasureOuterPartition
  simp_rw [anisotropicCavityInterpolationModel_potential]

theorem anisotropicRootVarianceResponse_rootCouplingScale (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : AnisotropicCouplingIndex n→Bool)
    (u : ℝ) (i : Fin n) (g : AnisotropicDisorder n) :
    anisotropicRootVarianceResponse (anisotropicScaleRootCouplings D p u) μ i g=
      anisotropicRootVarianceResponse D μ i (gaussianSelectedScale p u g) := by
  have he : (fun b=>anisotropicMeasurePotential
      (anisotropicReplaceVariance (anisotropicScaleRootCouplings D p u) i b) μ
        (anisotropicDisorderInjection n g))=
      (fun b=>anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ
        (anisotropicDisorderInjection n (gaussianSelectedScale p u g))) := by
    funext b
    rw [anisotropicReplaceVariance_scaleRootCouplings,anisotropicMeasurePotential_rootCouplingScale]
  have hl:=hasDerivAt_anisotropicMeasureTailPotential_variance_restart
    (anisotropicScaleRootCouplings D p u) μ i g ⟨0,by norm_num⟩ 0 (D.variance i) (D.variance_pos i)
  have hr:=hasDerivAt_anisotropicMeasureTailPotential_variance_restart
    D μ i (gaussianSelectedScale p u g) ⟨0,by norm_num⟩ 0 (D.variance i) (D.variance_pos i)
  simp only [anisotropicMeasureTailPotential_zero,map_zero,add_zero,anisotropicReplaceVariance_self] at hl hr
  have hs:=anisotropicReplaceVariance_self (anisotropicScaleRootCouplings D p u) i
  change anisotropicReplaceVariance (anisotropicScaleRootCouplings D p u) i (D.variance i)=
    anisotropicScaleRootCouplings D p u at hs
  rw [hs,he] at hl
  exact hl.unique hr

theorem anisotropicUnitCouplings_scaleRootCouplings (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) :
    anisotropicUnitCouplings (anisotropicScaleRootCouplings D p u)=anisotropicUnitCouplings D := rfl

theorem anisotropicCouplingRescaling_scaled_disorder (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) (g : AnisotropicDisorder n) :
    anisotropicCouplingRescaling (anisotropicScaleRootCouplings D p u) (anisotropicDisorderInjection n g)=
      anisotropicCouplingRescaling D (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) := by
  classical
  ext i
  cases i with
  | inl e =>
    by_cases hp:p e=true
    · simp [anisotropicCouplingRescaling,anisotropicScaleRootCouplings,anisotropicDisorderInjection,
        cavityGaussianSelectedScale_coordinate,hp,mul_assoc]
      ring
    · have hp0:p e=false:=Bool.eq_false_iff.mpr hp
      simp [anisotropicCouplingRescaling,anisotropicScaleRootCouplings,anisotropicDisorderInjection,
        cavityGaussianSelectedScale_coordinate,hp0]
  | inr i => simp [anisotropicCouplingRescaling,anisotropicDisorderInjection]

theorem anisotropicTailPairResponse_scaled_root (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : AnisotropicCouplingIndex n→Bool) (u : ℝ)
    (g : AnisotropicDisorder n) (e : AnisotropicCouplingIndex n) :
    anisotropicTailPairResponse (anisotropicScaleRootCouplings D p u) μ ⟨0,by norm_num⟩
        (anisotropicDisorderInjection n g) e=
      anisotropicTailPairResponse D μ ⟨0,by norm_num⟩
        (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e := by
  unfold anisotropicTailPairResponse
  rw [anisotropicUnitCouplings_scaleRootCouplings,anisotropicCouplingRescaling_scaled_disorder]

theorem anisotropicTailPairSecond_scaled_root (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : AnisotropicCouplingIndex n→Bool) (u : ℝ)
    (g : AnisotropicDisorder n) (e : AnisotropicCouplingIndex n) :
    anisotropicTailPairSecond (anisotropicScaleRootCouplings D p u) μ ⟨0,by norm_num⟩
        (anisotropicDisorderInjection n g) e=
      anisotropicTailPairSecond D μ ⟨0,by norm_num⟩
        (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) e := by
  unfold anisotropicTailPairSecond
  rw [anisotropicUnitCouplings_scaleRootCouplings,anisotropicCouplingRescaling_scaled_disorder]

end QuantitativeFollowup
