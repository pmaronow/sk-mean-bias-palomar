module
public import QuantitativeFollowup.FixedRowSymmetryPosteriorTransportHistory

@[expose] public section

/-! The chronological posterior and the retained line have exactly the same
normalized transition density. Consequently their full joint laws agree
after the explicit record reindexing, with no nondegeneracy assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
open SpinGlass.AT
open scoped BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 160000
set_option backward.isDefEq.respectTransparency false

variable {S I : Type} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

@[reducible] def cavityPosteriorLineTerminalSpin {E S : Type} :
    (N : ℕ) → Records E S (observationLinearTree N) → S
  | 0 => id
  | N+1 => fun z => cavityPosteriorLineTerminalSpin N z.2

theorem cavityLineTreeLogDensity_sum (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (N : ℕ) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S (observationLinearTree N)) :
    finiteCascadeTreeLogDensity V a L (observationLinearTree N) H z =
      (cavityFixedRowLineField N 0 H z) (cavityPosteriorLineTerminalSpin N z) +
        V (cavityPosteriorLineTerminalSpin N z) -
        gtStateLogPartition V (cavityFixedRowLineField N 0 H z) +
      ∑ i : Fin N, a (N-1-i) *
        (finiteStateGaussianTerminalCascade V a L (N-1-i)
            (cavityFixedRowLineField N (N-1-i) H z) -
          finiteStateGaussianTerminalCascade V a L (N-i)
            (cavityFixedRowLineField N (N-i) H z)) := by
  induction N generalizing H with
  | zero => simp [finiteCascadeTreeLogDensity, cavityFixedRowLineField]
  | succ N ih =>
      have hc (d : ℕ) (hd : d ≤ N) :
          cavityFixedRowLineField (N+1) d H z = cavityFixedRowLineField N d z.1 z.2 := by
        simp only [cavityFixedRowLineField, show d ≠ N+1 by omega, ite_false]
      have ht : cavityPosteriorLineTerminalSpin (N+1) z =
          cavityPosteriorLineTerminalSpin N z.2 := rfl
      rw [finiteCascadeTreeLogDensity]
      dsimp only
      rw [ih, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero, hc 0 (Nat.zero_le N), ht]
      have hroot : cavityFixedRowLineField (N+1) (N+1) H z = H := by
        simp only [cavityFixedRowLineField, ite_true]
      have hchild : cavityFixedRowLineField N N z.1 z.2 = z.1 := by
        cases N <;> simp [cavityFixedRowLineField]
      rw [hc N le_rfl, hchild, hroot]
      have he : (∑ i : Fin N, a (N-1-i) *
          (finiteStateGaussianTerminalCascade V a L (N-1-i)
            (cavityFixedRowLineField N (N-1-i) z.1 z.2) -
          finiteStateGaussianTerminalCascade V a L (N-i)
            (cavityFixedRowLineField N (N-i) z.1 z.2))) =
          ∑ i : Fin N, a (N+1-1-i.succ) *
          (finiteStateGaussianTerminalCascade V a L (N+1-1-i.succ)
            (cavityFixedRowLineField (N+1) (N+1-1-i.succ) H z) -
          finiteStateGaussianTerminalCascade V a L (N+1-i.succ)
            (cavityFixedRowLineField (N+1) (N+1-i.succ) H z)) := by
        apply Finset.sum_congr rfl
        intro i _
        have hsucc : (i.succ : ℕ) = (i : ℕ)+1 := rfl
        have h1 : N+1-1-(i.succ : ℕ)=N-1-i := by omega
        have h2 : N+1-(i.succ : ℕ)=N-i := by omega
        rw [h1,h2,hc _ (by omega),hc _ (by omega)]
      rw [he]
      simp only [Nat.add_sub_cancel] <;> ring

theorem cavityPosteriorLineRecord_terminal
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (N : ℕ) (H : FiniteStateField S) (z : (Fin N → FiniteStateGaussianInput I) × S) :
    cavityPosteriorLineTerminalSpin N (cavityPosteriorLineRecord L N H z) = z.2 := by
  induction N generalizing H with
  | zero => rfl
  | succ N ih => exact ih _ _

theorem cavityPosteriorLineRecord_logDensity {n : ℕ}
    (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → QuantitativePaper.Field n →L[ℝ] FiniteStateField S)
    (N : ℕ) (H : FiniteStateField S) (z : (Fin N → QuantitativePaper.Field n) × S) :
    finiteCascadeTreeLogDensity V a L (observationLinearTree N) H
        (cavityPosteriorLineRecord L N H z) =
      cascadePosteriorLogDensity V a L N H z := by
  rw [cavityLineTreeLogDensity_sum, cavityPosteriorLineRecord_terminal]
  have ht := cavityPosteriorLineRecord_field_history L N H z.1 z.2 (Fin.last N)
  simp only [Fin.val_last,Nat.sub_self] at ht
  rw [ht]
  unfold cascadePosteriorLogDensity cascadePosteriorHistoryPotential
  rw [show historyExtended (cascadePosteriorHistory L N H z.1) N =
      cascadePosteriorHistory L N H z.1 (Fin.last N) from
        historyExtended_fin _ (Fin.last N)]
  simp only [Fin.val_last,Nat.sub_self]
  rw [show finiteStateGaussianTerminalCascade V a L 0 = gtStateLogPartition V from rfl]
  have he : (∑ i : Fin N, a (N-1-i) *
        (finiteStateGaussianTerminalCascade V a L (N-1-i)
          (cavityFixedRowLineField N (N-1-i) H (cavityPosteriorLineRecord L N H z)) -
        finiteStateGaussianTerminalCascade V a L (N-i)
          (cavityFixedRowLineField N (N-i) H (cavityPosteriorLineRecord L N H z)))) =
      ∑ i : Fin N, a (N-1-i) *
        (finiteStateGaussianTerminalCascade V a L (N-(i+1))
          (historyExtended (cascadePosteriorHistory L N H z.1) (i+1)) -
        finiteStateGaussianTerminalCascade V a L (N-i)
          (historyExtended (cascadePosteriorHistory L N H z.1) i)) := by
    apply Finset.sum_congr rfl
    intro i _
    have hnext := cavityPosteriorLineRecord_field_history L N H z.1 z.2 i.succ
    have hnow := cavityPosteriorLineRecord_field_history L N H z.1 z.2 i.castSucc
    simp only [Fin.val_succ,Fin.val_castSucc] at hnext hnow
    have hd : N-((i:ℕ)+1)=N-1-i := by omega
    rw [hd] at hnext
    rw [hnext,hnow,historyExtended_left,historyExtended_right,hd]
  rw [he]
  ring

theorem cavityPosteriorGaussianLaw_map_lineRecord {n : ℕ}
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀j,0≤a j)
    (L : ℕ → QuantitativePaper.Field n →L[ℝ] FiniteStateField S)
    (N : ℕ) (H : FiniteStateField S) :
    (cascadePosteriorGaussianLaw V a L N H).map (cavityPosteriorLineRecord L N H) =
      finiteCascadeTreeRecordKernel V a L (observationLinearTree N) H := by
  haveI := isFiniteKernel_finiteCascadeTreeReferenceKernel L (observationLinearTree N)
  have hm : Measurable (cavityPosteriorLineRecord L N H) :=
    (measurable_cavityPosteriorLineRecord L N).comp (measurable_const.prodMk measurable_id)
  have hw : Measurable (fun z => ENNReal.ofReal
      (Real.exp (finiteCascadeTreeLogDensity V a L (observationLinearTree N) H z))) :=
    ((measurable_finiteCascadeTreeLogDensity V a ha L _).comp
      (measurable_const.prodMk measurable_id)).exp.ennreal_ofReal
  have he : cascadePosteriorGaussianLaw V a L N H =
      (cascadePosteriorGaussianBase S (Fin n) N).withDensity
        (fun z => ENNReal.ofReal (Real.exp
          (finiteCascadeTreeLogDensity V a L (observationLinearTree N) H
            (cavityPosteriorLineRecord L N H z)))) := by
    rw [cascadePosteriorGaussianLaw_eq_exp_density V a ha L N H]
    congr 1
    funext z
    rw [cavityPosteriorLineRecord_logDensity]
  rw [he,map_withDensity_pullback _ _ hm _ hw,cavityPosteriorLineRecord_raw_law,
    finiteCascadeTreeRecordKernel_exp_density V a ha L,
    Kernel.withDensity_apply _
      (measurable_finiteCascadeTreeLogDensity V a ha L _).exp.ennreal_ofReal]

end QuantitativeFollowup
