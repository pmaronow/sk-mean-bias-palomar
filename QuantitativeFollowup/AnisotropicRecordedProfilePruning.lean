module
public import QuantitativeFollowup.AnisotropicRecordedProfileLawConvergence
public import FourPapersCommon.FiniteObservationTreePairPruning

@[expose] public section

/-! Genuine marginal laws of selected descendants of the arbitrary-profile
recorded process. They preserve the actual common path and its split level. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy FiniteObservationPruning
variable {n : ℕ}
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

theorem anisotropicRecordedProfileTreeKernel_eq_observation (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) {J : ℕ} (T : FiniteTerminalGenealogy J) :
    anisotropicRecordedProfileTreeKernel D μ q T=observationTreeKernel
      (fun j=>anisotropicObservationTransition D μ (q (j+1)) (q j))
      ((anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
        (measurable_anisotropicObservationParameter D)) T := by
  induction T with
  | leaf => rfl
  | advance T ih => exact congrArg (fun K=>(Kernel.id ×ₖ K) ∘ₖ _) ih
  | fork T U ihT ihU => exact congrArg₂ (fun K L=>K ×ₖ L) ihT ihU

theorem anisotropicRecordedProfileTreeKernel_pruning (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) {J : ℕ}
    {T U : FiniteTerminalGenealogy J} (P : FiniteObservationPruning T U) :
    (anisotropicRecordedProfileTreeKernel D μ q T).map (project P)=
      anisotropicRecordedProfileTreeKernel D μ q U := by
  rw [anisotropicRecordedProfileTreeKernel_eq_observation,
    anisotropicRecordedProfileTreeKernel_eq_observation]
  exact observationTreeKernel_pruning _ (fun _=>inferInstance) _ P

theorem anisotropicRecordedProfileTreeLaw_pruning (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) {J : ℕ}
    {T U : FiniteTerminalGenealogy J} (P : FiniteObservationPruning T U) :
    (anisotropicRecordedProfileTreeLaw D μ a q T).map (Prod.map id (project P))=
      anisotropicRecordedProfileTreeLaw D μ a q U := by
  rw [anisotropicRecordedProfileTreeLaw,anisotropicRecordedProfileTreeLaw,
    ←Measure.compProd_map (measurable_project P),anisotropicRecordedProfileTreeKernel_pruning D μ q P]

theorem anisotropicRecordedProfileTreeKernel_leaf_marginal (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (i : ObservationLeaf T) :
    (anisotropicRecordedProfileTreeKernel D μ q T).map (observationLeafSpin T i)=
      (anisotropicRecordedProfileTreeKernel D μ q (observationLinearTree J)).map (observationLinearSpin J) := by
  rw [←observationLeafPruning_spin T i,
    Kernel.map_comp_right _ (measurable_project (observationLeafPruning T i))
      (measurable_observationLinearSpin J),anisotropicRecordedProfileTreeKernel_pruning]

theorem anisotropicRecordedProfileTreeKernel_pair_marginal (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (i k : ObservationLeaf T) (hik : i≠k) :
    ∃ P : ObservationPairTree J, P.splitLevel=observationCommonLevel T i k ∧
      (anisotropicRecordedProfileTreeKernel D μ q T).map
        (fun v=>(observationLeafSpin T i v,observationLeafSpin T k v))=
          (anisotropicRecordedProfileTreeKernel D μ q P.tree).map P.spins := by
  obtain ⟨P,R,hlevel,hspin⟩:=exists_observationPairPruning
    (E:=AnisotropicObservationState n) (S:=Configuration n) T i k hik
  refine ⟨P,hlevel,?_⟩
  rw [←hspin,Kernel.map_comp_right _ (measurable_project R) (P.measurable_spins),
    anisotropicRecordedProfileTreeKernel_pruning D μ q R]

theorem anisotropicRecordedProfileTreeLaw_pair_marginal (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (i k : ObservationLeaf T) (hik : i≠k) :
    ∃ P : ObservationPairTree J, P.splitLevel=observationCommonLevel T i k ∧
      (anisotropicRecordedProfileTreeLaw D μ a q T).map
        (fun v=>(v.1,(observationLeafSpin T i v.2,observationLeafSpin T k v.2)))=
          (anisotropicRecordedProfileTreeLaw D μ a q P.tree).map (Prod.map id P.spins) := by
  obtain ⟨P,R,hlevel,hspin⟩:=exists_observationPairPruning
    (E:=AnisotropicObservationState n) (S:=Configuration n) T i k hik
  refine ⟨P,hlevel,?_⟩
  have he : (fun v : AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) T=>
      (v.1,(observationLeafSpin T i v.2,observationLeafSpin T k v.2)))=
      (Prod.map id P.spins) ∘ Prod.map id (project R) := by
    funext v
    exact Prod.ext rfl (congrFun hspin v.2).symm
  rw [he,←Measure.map_map (measurable_id.prodMap P.measurable_spins)
    (measurable_id.prodMap (measurable_project R)),anisotropicRecordedProfileTreeLaw_pruning D μ a q R]

theorem tendsto_anisotropicRecordedProfile_pair_marginal {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure} (hμ : Tendsto μ l (𝓝 ν))
    (a : ℝ) (q : ℕ→Paper.Overlap) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (hq : ∀j,j<J→q (j+1)≤q j) (i k : ObservationLeaf T) :
    Tendsto (fun j=>(anisotropicRecordedProfileProbability D (μ j) a q T).map
      (fun v=>(v.1,(observationLeafSpin T i v.2,observationLeafSpin T k v.2)))) l
      (𝓝 ((anisotropicRecordedProfileProbability D ν a q T).map
        (fun v=>(v.1,(observationLeafSpin T i v.2,observationLeafSpin T k v.2))))) := by
  have hmap : Continuous (fun v : AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T=>
      (v.1,(observationLeafSpin T i v.2,observationLeafSpin T k v.2))) :=
    continuous_fst.prodMk (((continuous_observationLeafSpin T i).comp continuous_snd).prodMk
      ((continuous_observationLeafSpin T k).comp continuous_snd))
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_anisotropicRecordedProfileProbability D hμ a q T hq) hmap

end QuantitativeFollowup
