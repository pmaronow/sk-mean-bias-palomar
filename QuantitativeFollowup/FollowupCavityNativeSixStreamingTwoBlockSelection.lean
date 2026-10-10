module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelection

@[expose] public section

/-! Two ancestral fields in one refined edge are retained jointly with
its complete lower record.  Distinct ordered indices have the actual
three-transition law; equal indices retain the very same state. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {E S : Type} {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def nativeStreamingTwoBlockSelection {j : ℕ}
    (T : FiniteTerminalGenealogy j) (d p k : ℕ) :
    Records E S (.advance (observationTreePad T d)) → E × (E × (E × Records E S T)) :=
  fun z => ((nativeStreamingBlockSelectionAt T d p z).1,
    ((nativeStreamingBlockSelectionAt T d k z).1,observationBlockCollapse T d z))

theorem measurable_nativeStreamingTwoBlockSelection [MeasurableSpace E] [MeasurableSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (d p k : ℕ) :
    Measurable (nativeStreamingTwoBlockSelection (E:=E) (S:=S) T d p k) :=
  (measurable_nativeStreamingBlockSelectionAt T d p).fst.prodMk
    ((measurable_nativeStreamingBlockSelectionAt T d k).fst.prodMk
      (measurable_observationBlockCollapse T d))

theorem continuous_nativeStreamingTwoBlockSelection [TopologicalSpace E] [TopologicalSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (d p k : ℕ) :
    Continuous (nativeStreamingTwoBlockSelection (E:=E) (S:=S) T d p k) :=
  (continuous_nativeStreamingBlockSelectionAt T d p).fst.prodMk
    ((continuous_nativeStreamingBlockSelectionAt T d k).fst.prodMk
      (continuous_observationBlockCollapse T d))

theorem nativeStreamingTwoBlockSelection_equal {j : ℕ}
    (T : FiniteTerminalGenealogy j) (d p : ℕ) :
    nativeStreamingTwoBlockSelection (E:=E) (S:=S) T d p p=
      (fun z=> (z.1,(z.1,z.2))) ∘ nativeStreamingBlockSelectionAt T d p := by
  funext z
  simp only [Function.comp_apply,nativeStreamingTwoBlockSelection,
    nativeStreamingBlockSelectionAt_snd]

theorem nativeStreamingTwoBlockSelection_succ_lower {j : ℕ}
    (T : FiniteTerminalGenealogy j) (d p k : ℕ) (hp : p≠d) (hk : k≠d) :
    nativeStreamingTwoBlockSelection (E:=E) (S:=S) T (d+1) p k=
      nativeStreamingTwoBlockSelection T d p k ∘ Prod.snd := by
  funext z
  simp only [nativeStreamingTwoBlockSelection,nativeStreamingBlockSelectionAt,
    if_neg hp,if_neg hk,Function.comp_apply]

theorem nativeStreamingTwoBlockSelection_succ_top {j : ℕ}
    (T : FiniteTerminalGenealogy j) (d p : ℕ) (hp : p≠d) :
    nativeStreamingTwoBlockSelection (E:=E) (S:=S) T (d+1) p d=
      (fun z=> (z.2.1,(z.1,z.2.2))) ∘
        Prod.map id (nativeStreamingBlockSelectionAt T d p) := by
  funext z
  simp only [nativeStreamingTwoBlockSelection,nativeStreamingBlockSelectionAt,
    if_neg hp,if_pos rfl,Function.comp_apply,ite_true]
  dsimp only [Prod.map,observationBlockCollapse,Function.comp_apply]
  rw [nativeStreamingBlockSelectionAt_snd]
  try rfl

theorem nativeStreamingTwoBlockSelection_kernel_lt (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (Q : ℕ → Paper.Overlap) (hQ : Antitone Q)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (d p k : ℕ) (hpk : p<k) (hk : k<d) :
    (anisotropicRecordedProfileTreeKernel D μ Q (.advance (observationTreePad T d))).map
      (nativeStreamingTwoBlockSelection T d p k)=
      ((Kernel.id ×ₖ ((Kernel.id ×ₖ ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ Q T) ∘ₖ
        anisotropicObservationTransition D μ (Q (j+p+1)) (Q j))) ∘ₖ
          anisotropicObservationTransition D μ (Q (j+k+1)) (Q (j+p+1)))) ∘ₖ
            anisotropicObservationTransition D μ (Q (j+d+1)) (Q (j+k+1))).map
              (fun z=> (z.2.1,(z.1,z.2.2))) := by
  induction d generalizing p k with
  | zero => omega
  | succ d ih =>
      by_cases he:k=d
      · subst k
        have hp:p<d:=hpk
        have hne : ¬p=d := by omega
        rw [nativeStreamingTwoBlockSelection_succ_top T d p hne]
        change ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ Q
          (.advance (observationTreePad T d))) ∘ₖ
            anisotropicObservationTransition D μ (Q (j+(d+1)+1)) (Q (j+d+1))).map
          ((fun z : AnisotropicObservationState n × (AnisotropicObservationState n ×
              (AnisotropicObservationState n × Records (AnisotropicObservationState n)
                (Configuration n) T)) => (z.2.1,(z.1,z.2.2))) ∘
            Prod.map id (nativeStreamingBlockSelectionAt T d p))=_
        have hshuffle : Measurable (fun z : AnisotropicObservationState n ×
            (AnisotropicObservationState n ×
              (AnisotropicObservationState n × Records (AnisotropicObservationState n)
                (Configuration n) T)) => (z.2.1,(z.1,z.2.2))) :=
          measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)
        rw [Kernel.map_comp_right _
          (measurable_id.prodMap (measurable_nativeStreamingBlockSelectionAt T d p))
          hshuffle,
          Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
            (measurable_nativeStreamingBlockSelectionAt T d p),Kernel.map_id,
          nativeStreamingBlockSelectionAt_kernel D μ Q hQ T d p hp]
        try simp only [Nat.add_assoc]
      · have hk':k<d:=by omega
        have hp':p≠d:=by omega
        rw [nativeStreamingTwoBlockSelection_succ_lower T d p k hp' he]
        change ((_ ×ₖ _) ∘ₖ _).map
          (nativeStreamingTwoBlockSelection T d p k ∘ Prod.snd)=_
        rw [Kernel.map_comp,Kernel.map_comp_right _ measurable_snd
          (measurable_nativeStreamingTwoBlockSelection T d p k),←Kernel.snd_eq,Kernel.snd_prod,
          ih p k hpk hk',Kernel.map_comp,Kernel.comp_assoc]
        have hc:=anisotropicObservationTransition_semigroup D μ
          (Q (j+(d+1)+1)) (Q (j+d+1)) (Q (j+k+1))
          (hQ (by omega)) (hQ (by omega))
        simp only [Nat.add_assoc] at hc ⊢
        rw [hc,Kernel.map_comp]

end QuantitativeFollowup
