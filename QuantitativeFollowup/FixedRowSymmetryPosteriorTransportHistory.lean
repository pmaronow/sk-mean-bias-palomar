module
public import QuantitativeFollowup.FixedRowSymmetryPosteriorTransportCoordinates
public import QuantitativePaper.VectorHistoryLinear

@[expose] public section

/-! Every remaining-depth selector of the retained line is the corresponding
chronological posterior history field. The same field is an explicit affine
map of the original, uncompressed Gaussian coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 160000
set_option backward.isDefEq.respectTransparency false

theorem cavityIndependentHistory_head_tail {E Z : Type}
    (u : ℕ → E → Z → E) (N : ℕ) (H : E) (z : Fin (N+1) → Z)
    (i : Fin (N+1)) :
    independentHistory u (N+1) (H,z) i.succ =
      independentHistory (fun j => u (j+1)) N (u 0 H (z 0),Fin.tail z) i := by
  refine Fin.induction ?_ ?_ i
  · simpa only [Fin.castSucc_zero, Fin.val_zero, independentHistory_initial] using
      independentHistory_next u (N+1) (H,z) (0 : Fin (N+1))
  · intro j ih
    rw [independentHistory_next u (N+1) (H,z) j.succ,
      independentHistory_next (fun j => u (j+1)) N (u 0 H (z 0),Fin.tail z) j]
    have he : j.succ.castSucc = j.castSucc.succ := by ext; rfl
    rw [he, ih]
    simp only [Fin.val_succ, Fin.tail]

variable {S I : Type} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

theorem cavityPosteriorHistory_head_tail
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (N : ℕ) (H : FiniteStateField S) (z : Fin (N+1) → FiniteStateGaussianInput I)
    (i : Fin (N+1)) :
    cascadePosteriorHistory L (N+1) H z i.succ =
      cascadePosteriorHistory L N (H+L N (z 0)) (Fin.tail z) i := by
  have hu : (fun j => cascadePosteriorUpdate L (N+1) (j+1)) = cascadePosteriorUpdate L N := by
    funext j Q w
    unfold cascadePosteriorUpdate
    rw [show N+1-1-(j+1)=N-1-j by omega]
  unfold cascadePosteriorHistory
  simpa only [hu, cascadePosteriorUpdate, Nat.add_sub_cancel, Nat.sub_zero] using
    cavityIndependentHistory_head_tail (cascadePosteriorUpdate L (N+1)) N H z i

theorem cavityPosteriorLineRecord_field_history
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (N : ℕ) (H : FiniteStateField S) (z : Fin N → FiniteStateGaussianInput I)
    (sigma : S) (i : Fin (N+1)) :
    cavityFixedRowLineField N (N-i) H (cavityPosteriorLineRecord L N H (z,sigma)) =
      cascadePosteriorHistory L N H z i := by
  induction N generalizing H with
  | zero => rfl
  | succ N ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.val_zero, Nat.sub_zero, cavityFixedRowLineField, ite_true]
        exact (independentHistory_initial (cascadePosteriorUpdate L (N+1)) (N+1) (H,z)).symm
      · have hd : N+1-(j.succ : ℕ) = N-j := by simp
        have hn : N-j ≠ N+1 := by omega
        simp only [hd, cavityFixedRowLineField, hn, ite_false, cavityPosteriorLineRecord]
        rw [cavityPosteriorHistory_head_tail]
        exact ih _ _ j

theorem cavityPosteriorLineRecord_field
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (N d : ℕ) (hd : d ≤ N) (H : FiniteStateField S)
    (z : Fin N → FiniteStateGaussianInput I) (sigma : S) :
    cavityFixedRowLineField N d H (cavityPosteriorLineRecord L N H (z,sigma)) =
      cascadePosteriorHistory L N H z ⟨N-d,by omega⟩ := by
  have hh := cavityPosteriorLineRecord_field_history L N H z sigma ⟨N-d,by omega⟩
  have he : N-(N-d)=d := by omega
  simpa only [he] using hh

def cavityPosteriorHistoryUpdateLinear
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (N j : ℕ) :
    (FiniteStateField S × FiniteStateGaussianInput I) →L[ℝ] FiniteStateField S :=
  ContinuousLinearMap.fst ℝ _ _ + (L (N-1-j)).comp (ContinuousLinearMap.snd ℝ _ _)

def cavityPosteriorLineFieldLinear
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (N d : ℕ) :
    (Fin N → FiniteStateGaussianInput I) →L[ℝ] FiniteStateField S :=
  ((ContinuousLinearMap.proj (⟨N-d,by omega⟩ : Fin (N+1))).comp
    (independentHistoryLinear (cavityPosteriorHistoryUpdateLinear L N) N)).comp
    ((0 : (Fin N → FiniteStateGaussianInput I) →L[ℝ] FiniteStateField S).prod
      (ContinuousLinearMap.id ℝ _))

theorem cavityPosteriorLineFieldLinear_apply
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (N d : ℕ) (z : Fin N → FiniteStateGaussianInput I) :
    cavityPosteriorLineFieldLinear L N d z =
      cascadePosteriorHistory L N 0 z ⟨N-d,by omega⟩ := by
  have hu : (fun j x w => x + L (N-1-j) w) = cascadePosteriorUpdate L N := rfl
  simp only [cavityPosteriorLineFieldLinear, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.id_apply, independentHistoryLinear_apply,
    cavityPosteriorHistoryUpdateLinear, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    cascadePosteriorHistory]
  rw [hu]

theorem cavityPosteriorLineRecord_field_affine {n : ℕ}
    (L : ℕ → QuantitativePaper.Field n →L[ℝ] FiniteStateField S)
    (N d : ℕ) (hd : d ≤ N) (H : FiniteStateField S)
    (z : Fin N → QuantitativePaper.Field n) (sigma : S) :
    cavityFixedRowLineField N d H (cavityPosteriorLineRecord L N H (z,sigma)) =
      H + cavityPosteriorLineFieldLinear L N d z := by
  rw [cavityPosteriorLineRecord_field L N d hd,
    cascadePosteriorHistory_eq_initial_add, cavityPosteriorLineFieldLinear_apply]

end QuantitativeFollowup
