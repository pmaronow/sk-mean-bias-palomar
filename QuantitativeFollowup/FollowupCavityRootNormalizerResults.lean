module
public import QuantitativeFollowup.FollowupCavityRootNormalizerIncident
public import QuantitativeFollowup.FollowupCavityRootNormalizerFreshMarks
public import QuantitativeFollowup.FollowupCavityOverlapMarks

@[expose] public section

/-! Literal root-normalizer response with two genuine fresh terminal
continuations. The same physical overlap defect is used by the recorded
streaming identities. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

private theorem finite_marks_integrable {X S : Type*} [MeasurableSpace X]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (P : Measure (X×S)) [IsProbabilityMeasure P] (f : S→ℝ) :
    Integrable (fun z=>f z.2) P :=
  (integrable_const (∑s,‖f s‖)).mono' ((measurable_of_finite f).comp measurable_snd).aestronglyMeasurable
    (.of_forall fun z=>Finset.single_le_sum (fun s _=>norm_nonneg (f s)) (Finset.mem_univ z.2))

theorem anisotropicFreshTerminalPairLaw_overlapDefect
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    (∫z,cavitySpinOverlapDefect n q z.2.1 z.2.2∂anisotropicFreshTerminalPairLaw D μ a q)=
      (∑i : Fin n,∫p,(anisotropicProcessPairResponse D μ q (followupCavityIncidentIndex i) p)^2
        ∂anisotropicMeasureSampleLaw D μ a)/(n:ℝ)-
      (q:ℝ)*(∫p,(anisotropicProcessSpinResponse D μ q (Fin.last n) p)^2
        ∂anisotropicMeasureSampleLaw D μ a) := by
  classical
  let P:=anisotropicFreshTerminalPairLaw D μ a q
  let F:=fun (i : Fin n) (z : (AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1))×
      (Configuration (n+1)×Configuration (n+1)))=>
    anisotropicCouplingFeature (cavityIncidentEdge i) z.2.1*
      anisotropicCouplingFeature (cavityIncidentEdge i) z.2.2
  let G:=fun z : (AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1))×
      (Configuration (n+1)×Configuration (n+1))=>
    Paper.spinSign (z.2.1 (Fin.last n))*Paper.spinSign (z.2.2 (Fin.last n))
  have hF (i : Fin n) : Integrable (F i) P:=finite_marks_integrable P
    (fun z : Configuration (n+1)×Configuration (n+1)=>
      anisotropicCouplingFeature (cavityIncidentEdge i) z.1*
        anisotropicCouplingFeature (cavityIncidentEdge i) z.2)
  have hG : Integrable G P:=finite_marks_integrable P
    (fun z : Configuration (n+1)×Configuration (n+1)=>
      Paper.spinSign (z.1 (Fin.last n))*Paper.spinSign (z.2 (Fin.last n)))
  have he : (fun z=>cavitySpinOverlapDefect n q z.2.1 z.2.2)=
      (fun z=>(∑i,F i z)/(n:ℝ)-(q:ℝ)*G z) := by
    funext z
    simp only [cavitySpinOverlapDefect,cavityCoordinateFeature_apply,F,G]
    ring
  rw [he,integral_sub ((integrable_finset_sum _ (fun i _=>hF i)).div_const _) (hG.const_mul _),
    integral_div,integral_finset_sum _ (fun i _=>hF i),integral_const_mul]
  have hFi (i : Fin n) : (∫z,F i z∂P)=
      ∫p,(anisotropicProcessPairResponse D μ q (followupCavityIncidentIndex i) p)^2
        ∂anisotropicMeasureSampleLaw D μ a :=
    anisotropicFreshTerminalPairLaw_pair_square D μ a q (followupCavityIncidentIndex i)
  have hGi : (∫z,G z∂P)=∫p,(anisotropicProcessSpinResponse D μ q (Fin.last n) p)^2
      ∂anisotropicMeasureSampleLaw D μ a :=anisotropicFreshTerminalPairLaw_spin_square D μ a q _
  simp_rw [hFi,hGi]

theorem hasDerivAt_log_followupCavityRootPartition
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (u : ℝ) (hu : u∈Ioc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u ⟨hu.1.le,hu.2⟩
    HasDerivAt (fun v=>Real.log (followupCavityRootPartition n β ρ hβ hρ μ a v))
      (-a*followupCavityAlpha n β ρ/2*
        (∫r : Paper.Overlap,∫z,cavitySpinOverlapDefect n r z.2.1 z.2.2
          ∂anisotropicFreshTerminalPairLaw D μ a r∂parisiFreeMeasure μ a)) u := by
  dsimp only
  simpa only [anisotropicFreshTerminalPairLaw_overlapDefect] using
    hasDerivAt_log_followupCavityRootPartition_future_squares hn β ρ hβ hρ μ a ha hμ u hu

theorem followup_cavity_root_normalizer_response
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Ioc (0:ℝ) (1/2)) (hμ : μ∈scalarFloor a)
    (u : ℝ) (hu : u∈Ioo (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u ⟨hu.1.le,hu.2.le⟩
    followupCavityRootPartition n β ρ hβ hρ μ a u=anisotropicMeasureOuterPartition D μ a ∧
    HasDerivAt (fun v=>Real.log (followupCavityRootPartition n β ρ hβ hρ μ a v))
      (-a*followupCavityAlpha n β ρ/2*
        (∫r : Paper.Overlap,∫z,Paper.spinSign (z.2.1 (Fin.last n))*Paper.spinSign (z.2.2 (Fin.last n))*
          ((∑i : Fin n,Paper.spinSign (z.2.1 i.castSucc)*Paper.spinSign (z.2.2 i.castSucc))/(n:ℝ)-(r:ℝ))
            ∂anisotropicFreshTerminalPairLaw D μ a r∂parisiFreeMeasure μ a)) u := by
  dsimp only
  constructor
  · exact followupCavityRootPartition_eq_actual β ρ hβ hρ μ a u ⟨hu.1.le,hu.2.le⟩
  · simpa only [cavitySpinOverlapDefect_eq] using
      hasDerivAt_log_followupCavityRootPartition hn β ρ hβ hρ μ a ⟨ha.1.le,by linarith [ha.2]⟩ hμ u ⟨hu.1,hu.2.le⟩

end QuantitativeFollowup
