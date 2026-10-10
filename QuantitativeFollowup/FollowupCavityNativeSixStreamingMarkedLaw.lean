module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingObservationGraft
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingInsertion
public import QuantitativeFollowup.AnisotropicRecordedPairCollapse

@[expose] public section

/-! Every native ancestral mark is an actual independent restarted
continuation, jointly with the complete original record. The enlarged
genealogy realizes this kernel exactly, for arbitrary profiles. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingRecordedProfileTreeKernel_eq_observation (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J) :
    anisotropicRecordedProfileTreeKernel D μ q T=
      observationTreeKernel (fun j=>anisotropicObservationTransition D μ (q (j+1)) (q j))
        ((anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
          (measurable_anisotropicObservationParameter D)) T := by
  induction T with
  | leaf => rfl
  | advance T ih =>
      simp only [anisotropicRecordedProfileTreeKernel,observationTreeKernel,ih]
  | fork T U ihT ihU =>
      simp only [anisotropicRecordedProfileTreeKernel,observationTreeKernel,ihT,ihU]

def nativeStreamingSingleVertexKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) :
    Kernel (AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) T)
      (Configuration n) :=
  (anisotropicObservationTerminalSpinKernel D μ (q v.depth)).comap
    (Function.uncurry (nativeStreamingVertexState v)) (nativeStreamingVertexState_measurable v)

instance nativeStreamingSingleVertexKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) :
    IsMarkovKernel (nativeStreamingSingleVertexKernel D μ q T v) := by
  unfold nativeStreamingSingleVertexKernel
  infer_instance

def nativeStreamingSingleVertexLaw (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) :=
  anisotropicRecordedProfileTreeLaw D μ a q T ⊗ₘ nativeStreamingSingleVertexKernel D μ q T v

instance nativeStreamingSingleVertexLaw_probability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) :
    IsProbabilityMeasure (nativeStreamingSingleVertexLaw D μ a q T v) := by
  unfold nativeStreamingSingleVertexLaw
  infer_instance

theorem nativeStreamingSingleVertexLaw_fst (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) :
    (nativeStreamingSingleVertexLaw D μ a q T v).fst=anisotropicRecordedProfileTreeLaw D μ a q T :=
  Measure.fst_compProd _ _

theorem nativeStreamingSingleVertexLaw_eq_graft (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (hzero : q 0=1) (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :
    (anisotropicRecordedProfileTreeLaw D μ a q
      (finiteCascadeContinuationGraft observationLinearTree v)).map
        (fun z=>((z.1,(finiteCascadeContinuationExtract observationLinearTree observationLinearSpin v z.2).1),
          (finiteCascadeContinuationExtract observationLinearTree observationLinearSpin v z.2).2))=
      nativeStreamingSingleVertexLaw D μ a q T v := by
  let κ:ℕ→Kernel (AnisotropicObservationState n) (AnisotropicObservationState n):=
    fun j=>anisotropicObservationTransition D μ (q (j+1)) (q j)
  let θ:Kernel (AnisotropicObservationState n) (Configuration n):=
    (anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
      (measurable_anisotropicObservationParameter D)
  have hκ:∀j,IsMarkovKernel (κ j):=fun _=>inferInstance
  haveI:IsMarkovKernel θ:=inferInstance
  have hc (j:ℕ) : nativeStreamingContinuationKernel κ θ observationLinearTree observationLinearSpin j=
      anisotropicObservationTerminalSpinKernel D μ (q j) := by
    unfold nativeStreamingContinuationKernel
    rw [←nativeStreamingRecordedProfileTreeKernel_eq_observation D μ q]
    exact anisotropicRecordedLinearSpinKernel D μ q hzero j (fun i _=>hq (Nat.le_succ i))
  have hv : nativeStreamingContinuationVertexKernel κ θ observationLinearTree observationLinearSpin v=
      nativeStreamingSingleVertexKernel D μ q T v := by
    unfold nativeStreamingContinuationVertexKernel nativeStreamingSingleVertexKernel
    rw [hc]
  have hg:=nativeStreamingObservationGraft_joint_law κ hκ θ observationLinearTree observationLinearSpin
    (fun j=>measurable_observationLinearSpin j) v (anisotropicObservationInitialLaw D μ a)
  rw [←nativeStreamingRecordedProfileTreeKernel_eq_observation D μ q,
    nativeStreamingContinuationMarkedLaw,←nativeStreamingRecordedProfileTreeKernel_eq_observation D μ q,hv] at hg
  exact hg

end QuantitativeFollowup
