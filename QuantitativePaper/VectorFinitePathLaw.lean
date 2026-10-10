module
public import QuantitativePaper.VectorFiniteRestrictedLaw
public import FourPapersCommon.FiniteHistoryPrefix

@[expose] public section

/-! The literal finite node history of the constructed Wiener/Picard
vector diffusion equals the separately constructed branching path measure.
The proof retains the whole past at each chronological induction step. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

@[simp] theorem vectorOuterLaw_zero (s : RSBScheme k) (β t : ℝ) :
    vectorOuterLaw (n:=n) s β t 0=completionLaw n := by
  have hp : vectorOuterPartition (n:=n) s β t 0=1 := by
    simp [vectorOuterPartition]
  simp [vectorOuterLaw,vectorOuterWeight,hp]

theorem vectorFiniteJointState_initial_law (s : RSBScheme k) (β t : ℝ) (ht : t≤1) :
    (vectorDisorderBrownianMeasure n).map (vectorFiniteJointState s β t ht 0)=
      vectorInitialLaw s β t 0 := by
  rw [vectorInitialLaw,vectorOuterLaw_zero,
    ←(hasLaw_initialVectorDisorder n).map_eq,
    Measure.map_map (by fun_prop) measurable_fst]
  congr 1
  funext sample
  simp [vectorFiniteJointState,vectorFiniteState_zero,Function.comp_def]

def vectorFiniteHistory (s : RSBScheme k) (β t : ℝ) (ht : t≤1) (j : ℕ)
    (sample : VectorDisorderBrownianSample n) : FiniteHistory (VectorState n) j :=
  historySample (vectorFiniteJointState s β t ht) (fun i=>(s.q i).toNNReal) j sample

theorem measurable_vectorFiniteHistory (s : RSBScheme k) (β t : ℝ) (ht : t≤1) (j : ℕ) :
    Measurable (vectorFiniteHistory (n:=n) s β t ht j) :=
  measurable_historySample _ (measurable_vectorFiniteJointState s β t ht) _ _

theorem vectorFiniteHistory_law (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (j : ℕ) (hj : j≤k+2) :
    (vectorDisorderBrownianMeasure n).map (vectorFiniteHistory s β t ht.le j)=
      finiteHistoryLaw (vectorInitialLaw s β t 0) (vectorProfileKernel s β t) j := by
  have he := historySample_law_of_restricted_up_to
    (vectorDisorderBrownianMeasure n) (vectorBrownianFiltration n)
    (vectorFiniteJointState s β t ht.le) (adapted_vectorFiniteJointState s β t ht.le)
    (fun i=>(s.q i).toNNReal) (k+2)
    (fun a b hab hb=>Real.toNNReal_le_toNNReal (s.q_mono' b hb a hab))
    (vectorProfileKernel s β t) (vectorProfileKernel_markov s β t)
    (fun i hi A hA=>vectorFinite_restricted_transition_law s β t hβ ht i (by omega) A hA)
    j hj
  change (vectorDisorderBrownianMeasure n).map
    (historySample (vectorFiniteJointState s β t ht.le) (fun i=>(s.q i).toNNReal) j)=_
  simpa only [s.q_zero,Real.toNNReal_zero,vectorFiniteJointState_initial_law] using he

theorem vectorFinite_full_history_law (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) :
    (vectorDisorderBrownianMeasure n).map (vectorFiniteHistory s β t ht.le (k+2))=
      vectorFieldHistoryLaw s β t 0 :=
  vectorFiniteHistory_law s β t hβ ht (k+2) le_rfl

end QuantitativePaper
