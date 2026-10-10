module
public import QuantitativeFollowup.ScalarAmplitudeMarkedSmooth
public import QuantitativeFollowup.ScalarTransportAmplitude
public import QuantitativeFollowup.ScalarObservationRefinement

@[expose] public section

/-! The finite-profile smoothness clause in Lemma 6.3: the literal
transported physical diffusion moment is genuinely C∞ in a neighborhood
of every sufficiently small covariance parameter. The proof includes
repeated physical levels and all observation overlaps. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff InnerProductSpace NNReal BigOperators
namespace QuantitativeFollowup
open Paper QuantitativePaper FourPapersCommon SpinGlass.Targets FRSB
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem scalarAmplitudeMarkedIntegrand_eq_transport (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (p : Fin (k+3)) (e : Bool) (z : QuantitativePaper.Field (k+2)) :
    scalarAmplitudeMarkedIntegrand s p e (scalarTransportAmplitude s β φ u,z,0)=
      Real.exp (scalarTransportEuclideanExponent s β φ e u
        (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2) z))*
        scalarTransportGradientSquare s β φ p u
          (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2) z) := by
  have hex : scalarAmplitudeMarkedExponent s e (scalarTransportAmplitude s β φ u,z,0)=
      scalarTransportEuclideanExponent s β φ e u
        (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2) z) := by
    unfold scalarAmplitudeMarkedExponent scalarTransportEuclideanExponent
    have hfield : scalarAmplitudeField (scalarTransportAmplitude s β φ u,z,0)=
        scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2) z (Fin.last (k+2)) :=
      scalarAmplitudeField_eq_history_last (scalarSchemeTransportCoefficient s β φ u) (k+2) z
    rw [hfield]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hh := scalarTransportAmplitude_node_potential s β hβ φ L hφ h0 h1 u hu
      (⟨i+1,by omega⟩ : Fin (k+3)) z
    exact congrArg (fun y : ℝ => (s.m (i+1)-s.m i)*y) hh
  rw [scalarAmplitudeMarkedIntegrand,hex,scalarTransportAmplitude_node_gradient s β hβ φ L hφ h0 h1 u hu p z]
  rfl

theorem scalarTransportGamma_eq_amplitudeGamma (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (p : Fin (k+3)) :
    Gamma β (scalarTransportMeasure (parisiSchemeMeasure s) φ u)
      (scalarLevelTransport φ u (scalarSchemeTransportNode s p))=
      scalarAmplitudeGamma s p (scalarTransportAmplitude s β φ u,0,0) := by
  rw [scalarTransportGaussian_Gamma s β hβ φ L hφ h0 h1 u hu p]
  unfold scalarAmplitudeGamma gaussianShiftAverage
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  apply integral_congr_ae
  filter_upwards [] with z
  have he : (scalarTransportAmplitude s β φ u,0,0)+scalarAmplitudeNoiseShift (k+2) z=
      (scalarTransportAmplitude s β φ u,z,0) := by
    simp only [scalarAmplitudeNoiseShift_apply,Prod.mk_add_mk,add_zero,zero_add]
  rw [he]
  exact (scalarAmplitudeMarkedIntegrand_eq_transport s β hβ φ L hφ h0 h1 u hu p e z).symm

theorem contDiffAt_scalarTransportGamma_node (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (p : Fin (k+3)) (u : ℝ) (hu : |u| *L<1) :
    ContDiffAt ℝ ∞ (fun v => Gamma β (scalarTransportMeasure (parisiSchemeMeasure s) φ v)
      (scalarLevelTransport φ v (scalarSchemeTransportNode s p))) u := by
  have hcurve : ContDiffAt ℝ ∞ (fun v : ℝ => ((scalarTransportAmplitude s β φ v,0,0) : ScalarAmplitudeState (k+2))) u :=
    (contDiffAt_scalarTransportAmplitude s β hβ φ L hφ h0 h1 u hu).prodMk
      ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : QuantitativePaper.Field (k+2))) u).prodMk
        (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) u))
  have hs := (contDiffAt_scalarAmplitudeGamma s p (scalarTransportAmplitude s β φ u,0,0)).comp u hcurve
  apply hs.congr_of_eventuallyEq
  have hnb : {v : ℝ | |v| *(L:ℝ)<1} ∈ 𝓝 u :=
    (isOpen_lt (continuous_abs.mul continuous_const) continuous_const).mem_nhds hu
  filter_upwards [hnb] with v hv
  exact scalarTransportGamma_eq_amplitudeGamma s β hβ φ L hφ h0 h1 v hv p

theorem contDiffAt_scalarTransportGamma (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (p : Paper.Overlap) (u : ℝ) (hu : |u| *L<1) :
    ContDiffAt ℝ ∞ (fun v => Gamma β (scalarTransportMeasure (parisiSchemeMeasure s) φ v)
      (scalarLevelTransport φ v p)) u := by
  obtain ⟨K,r,j,hm,hq⟩ := exists_scalar_same_measure_scheme_node s p
  have hs := contDiffAt_scalarTransportGamma_node r β hβ φ L hφ h0 h1 j u hu
  simpa only [hm,hq] using hs

theorem contDiffOn_scalarTransportGamma (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (p : Paper.Overlap) :
    ContDiffOn ℝ ∞ (fun v => Gamma β (scalarTransportMeasure (parisiSchemeMeasure s) φ v)
      (scalarLevelTransport φ v p)) {v : ℝ | |v| *(L:ℝ)<1} :=
  fun u hu => (contDiffAt_scalarTransportGamma s β hβ φ L hφ h0 h1 p u hu).contDiffWithinAt

end QuantitativeFollowup
