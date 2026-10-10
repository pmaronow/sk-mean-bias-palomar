module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTerminalMarkMoments

@[expose] public section

/-! Weak marked-law limits also retain terminal observables whose finitely
many coefficients move with the profile or insertion time.  All test
integrability and the error estimate come from the finite spin space. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ} {A : Type}
  [Fintype A] [MeasurableSpace A] [TopologicalSpace A]
  [DiscreteTopology A] [BorelSpace A] [SecondCountableTopology A]
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem integrable_nativeStreamingTerminalMarkTest {T : FiniteTerminalGenealogy J}
    (P : ProbabilityMeasure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) × A))
    (G : TerminalSpins (Configuration n) T × A → ℝ) :
    Integrable (fun z => G (finiteCascadeRecordTerminalSpins T z.1.2,z.2))
      (P : Measure ((AnisotropicObservationState n ×
        Records (AnisotropicObservationState n) (Configuration n) T) × A)) := by
  classical
  have hc : Continuous (fun z : ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) × A) =>
      G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (continuous_of_discreteTopology (f := G)).comp
      (((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_fst.snd).prodMk
        continuous_snd)
  apply (integrable_const (nativeStreamingTerminalMarkBound T G)).mono'
    hc.aestronglyMeasurable
  exact .of_forall fun z =>
    Finset.single_le_sum (fun σ _ => norm_nonneg (G σ)) (Finset.mem_univ _)

theorem nativeStreamingTerminalMarkMoment_sub {T : FiniteTerminalGenealogy J}
    (P : ProbabilityMeasure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) × A))
    (G H : TerminalSpins (Configuration n) T × A → ℝ) :
    nativeStreamingTerminalMarkMoment P G - nativeStreamingTerminalMarkMoment P H =
      nativeStreamingTerminalMarkMoment P (fun σ => G σ - H σ) := by
  unfold nativeStreamingTerminalMarkMoment
  exact (integral_sub (integrable_nativeStreamingTerminalMarkTest P G)
    (integrable_nativeStreamingTerminalMarkTest P H)).symm

theorem tendsto_nativeStreamingMovingTerminalMarkMoment
    {L : Type*} {l : Filter L} {T : FiniteTerminalGenealogy J}
    {Pj : L → ProbabilityMeasure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) × A)}
    {P : ProbabilityMeasure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) × A)}
    (hP : Tendsto Pj l (𝓝 P))
    (Gj : L → TerminalSpins (Configuration n) T × A → ℝ)
    (G : TerminalSpins (Configuration n) T × A → ℝ)
    (hG : ∀σ, Tendsto (fun N => Gj N σ) l (𝓝 (G σ))) :
    Tendsto (fun N => nativeStreamingTerminalMarkMoment (Pj N) (Gj N)) l
      (𝓝 (nativeStreamingTerminalMarkMoment P G)) := by
  classical
  have hb : Tendsto (fun N => nativeStreamingTerminalMarkBound T
      (fun σ => Gj N σ - G σ)) l (𝓝 0) := by
    unfold nativeStreamingTerminalMarkBound
    convert tendsto_finset_sum Finset.univ (fun σ _ => ((hG σ).sub tendsto_const_nhds).norm)
      using 1 <;> simp only [sub_self,norm_zero,Finset.sum_const_zero]
  have hd : Tendsto (fun N => nativeStreamingTerminalMarkMoment (Pj N) (Gj N) -
      nativeStreamingTerminalMarkMoment (Pj N) G) l (𝓝 0) := by
    apply squeeze_zero_norm (fun N => ?_) hb
    rw [nativeStreamingTerminalMarkMoment_sub]
    simpa only [Real.norm_eq_abs] using
      nativeStreamingTerminalMarkMoment_abs_le (Pj N) (fun σ => Gj N σ - G σ)
  simpa only [sub_add_cancel,zero_add] using
    hd.add (tendsto_nativeStreamingTerminalMarkMoment hP G)

end QuantitativeFollowup
