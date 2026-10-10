module
public import QuantitativePaper.VectorProfilePosteriorScoreBound
public import QuantitativePaper.VectorRestartFieldEnvelope
public import QuantitativePaper.VectorRestartGridPathLaw

@[expose] public section

/-! The genuine Gaussian posterior field history is the genuine restarted
diffusion history. This identifies its path envelope without an assumed
posterior moment or transition formula. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def vectorHistoryFieldDisplacement (x : Field n) {L : ℕ}
    (history : FiniteHistory (VectorState n) L) : ℝ :=
  ‖fun i : Fin (L+1)=>(history i).2-x‖

theorem continuous_vectorHistoryFieldDisplacement (x : Field n) (L : ℕ) :
    Continuous (vectorHistoryFieldDisplacement x (L:=L)) :=
  (continuous_pi fun i=>(continuous_snd.comp (continuous_apply i)).sub continuous_const).norm

theorem vectorTailGaussianPosterior_field_history_law (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (x : Field n) (L : ℕ) :
    (vectorTailGaussianPosterior s β t p x L).map
      (fun z=>vectorHistoryFrom s β t (k+2-L) p x L z.1)=
      vectorTailFieldLaw s β t p x L := by
  have he:=congrArg (fun P : Measure (FiniteHistory (VectorState n) L×Configuration n)=>P.map Prod.fst)
    (vectorTailGaussianPosterior_map s β t p x L)
  rw [Measure.map_map measurable_fst (measurable_vectorTailCoordinateJointMap s β t p x L),
    vectorTailPosteriorLaw,←Measure.fst,Measure.fst_compProd] at he
  exact he

theorem vectorRestartGridElapsed_le_one (μ : Paper.ParisiMeasure) (j : ℕ)
    (q : Paper.Overlap) (i : ℕ) (hi : i≤vectorDyadicIndex j+3) :
    vectorRestartGridElapsed μ j q i≤1 := by
  unfold vectorRestartGridElapsed
  rw [←Real.toNNReal_one]
  apply Real.toNNReal_le_toNNReal
  have hs:=(Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q_le_one hi
  have hmax : max (q:ℝ) ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)≤1 :=
    max_le q.property.2 hs
  linarith [q.property.1]

theorem vectorRestartGridHistory_displacement_le_envelope (μ : Paper.ParisiMeasure)
    (j : ℕ) (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ)
    (x : Field n) (sample : VectorDisorderBrownianSample n) :
    vectorHistoryFieldDisplacement x
      (vectorRestartGridHistory μ j β t ht q p x (vectorDyadicIndex j+3) sample)≤
      vectorRestartFieldPathEnvelope β t sample := by
  unfold vectorHistoryFieldDisplacement
  rw [pi_norm_le_iff_of_nonneg (vectorRestartFieldPathEnvelope_nonneg β t ht sample)]
  intro i
  exact norm_vectorRestartState_sub_initial_le_pathEnvelope _ β t ht q p x
    (vectorRestartGridElapsed μ j q i)
    (vectorRestartGridElapsed_le_one μ j q i (by have h:=i.isLt; omega)) sample

theorem measurable_vectorRestartGridHistory_full (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    Measurable (vectorRestartGridHistory μ j β t ht q p x (vectorDyadicIndex j+3)) :=
  measurable_historySample _
    (fun r=>(adapted_vectorRestartJointState _ β t ht q p x r).mono
      ((vectorBrownianFiltration n).le _) le_rfl) _ _

theorem vectorClampedGridPosterior_field_history_law (μ : Paper.ParisiMeasure)
    (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) :
    (vectorTailGaussianPosterior
      (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
      β t p x (vectorDyadicIndex j+3)).map
        (fun z=>vectorHistoryFrom
          (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
          β t 1 p x (vectorDyadicIndex j+3) z.1)=
    (vectorDisorderBrownianMeasure n).map
      (vectorRestartGridHistory μ j β t ht.le q p x (vectorDyadicIndex j+3)) := by
  rw [vectorRestartGrid_full_history_law μ j β t hβ ht q p x]
  have hL : vectorDyadicIndex j+1+1+2-(vectorDyadicIndex j+3)=1 := by omega
  simpa only [hL] using vectorTailGaussianPosterior_field_history_law
    (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
    β t p x (vectorDyadicIndex j+3)

end QuantitativePaper
