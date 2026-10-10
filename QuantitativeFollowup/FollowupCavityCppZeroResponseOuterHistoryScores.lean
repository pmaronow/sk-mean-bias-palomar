module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterScore
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterHistory

@[expose] public section

/-! The genuine free-Stieltjes scores are functions of the complete retained
history and terminal spin. Every charge keeps its actual history position,
including the zero-variance initial interval. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityOuterChargePosition (N : ℕ) : Option (Option (Fin N))→ℕ
  | none=>N+1
  | some none=>0
  | some (some i)=>(i:ℕ)+1

private theorem outer_charge_potential_translate (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ) (z : Fin (N+1)→Field n)
    (B : FiniteStateField S) (i : Option (Option (Fin N))) :
    (fun H=>cascadePosteriorStieltjesPotential V a L N z i (H+B))=
      fun H=>finiteStateGaussianTerminalCascade V a L (N+1-cavityOuterChargePosition N i)
        (H+(B+cascadePosteriorHistory L (N+1) 0 z (Fin.ofNat (N+2) (cavityOuterChargePosition N i)))) :=by
  cases i with
  | none=>
    dsimp only [cascadePosteriorStieltjesPotential,cavityOuterChargePosition]
    funext H
    have he:=congrFun (cascadePosteriorHistoryPotential_eq_translate V a L (N+1) (N+1) z) (H+B)
    simpa only [add_assoc] using he
  | some i=>cases i with
    | none=>
      dsimp only [cascadePosteriorStieltjesPotential,cavityOuterChargePosition]
      funext H
      have he:=congrFun (cascadePosteriorHistoryPotential_eq_translate V a L (N+1) 0 z) (H+B)
      simpa only [add_assoc] using he
    | some i=>
      dsimp only [cascadePosteriorStieltjesPotential,cavityOuterChargePosition]
      funext H
      have he:=congrFun (cascadePosteriorHistoryPotential_eq_translate V a L (N+1) ((i:ℕ)+1) z) (H+B)
      simpa only [add_assoc] using he

theorem cavityOuterStieltjesPotential_first_eq_history (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ) (z : Fin (N+1)→Field n)
    (B H K : FiniteStateField S) (i : Option (Option (Fin N))) :
    fderiv ℝ (fun Q=>cascadePosteriorStieltjesPotential V a L N z i (Q+B)) H K=
      fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N+1-cavityOuterChargePosition N i))
        (cascadePosteriorHistory L (N+1) (H+B) z (Fin.ofNat (N+2) (cavityOuterChargePosition N i))) K :=by
  rw [outer_charge_potential_translate,fderiv_comp_add_right]
  rw [cascadePosteriorHistory_eq_initial_add L (N+1) (H+B) z
    (Fin.ofNat (N+2) (cavityOuterChargePosition N i))]
  simp only [add_assoc]

theorem cavityOuterStieltjesPotential_second_eq_history (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ) (z : Fin (N+1)→Field n)
    (B H K : FiniteStateField S) (i : Option (Option (Fin N))) :
    fderiv ℝ (fun Q=>fderiv ℝ (fun Q=>cascadePosteriorStieltjesPotential V a L N z i (Q+B)) Q K) H K=
      fderiv ℝ (fun Q=>fderiv ℝ
        (finiteStateGaussianTerminalCascade V a L (N+1-cavityOuterChargePosition N i)) Q K)
        (cascadePosteriorHistory L (N+1) (H+B) z (Fin.ofNat (N+2) (cavityOuterChargePosition N i))) K :=by
  rw [outer_charge_potential_translate]
  simp_rw [fderiv_comp_add_right]
  change fderiv ℝ (fun Q=>fderiv ℝ
      (finiteStateGaussianTerminalCascade V a L (N+1-cavityOuterChargePosition N i))
      (Q+(B+cascadePosteriorHistory L (N+1) 0 z
        (Fin.ofNat (N+2) (cavityOuterChargePosition N i)))) K) H K=_
  rw [fderiv_comp_add_right (𝕜:=ℝ)
    (f:=fun Q=>fderiv ℝ
      (finiteStateGaussianTerminalCascade V a L (N+1-cavityOuterChargePosition N i)) Q K)
    (x:=H) (B+cascadePosteriorHistory L (N+1) 0 z
      (Fin.ofNat (N+2) (cavityOuterChargePosition N i)))]
  rw [cascadePosteriorHistory_eq_initial_add L (N+1) (H+B) z
    (Fin.ofNat (N+2) (cavityOuterChargePosition N i))]
  simp only [add_assoc]

theorem cavityOuterPosteriorScore_eq_history (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H K : FiniteStateField S)
    (p : FiniteStateGaussianInput J×((Fin (N+1)→Field n)×S)) :
    cavityOuterPosteriorScore V a L s N R H K p=
      K p.2.2-∑i,cavityOuterStieltjesWeight a s N i*
        fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N+1-cavityOuterChargePosition N i))
          ((cavityOuterHistoryMap L (N+1) R H p).1
            (Fin.ofNat (N+2) (cavityOuterChargePosition N i))) K-
        fderiv ℝ (fun Q=>Real.log (cavityOuterPosteriorNormalizer V a L s (N+1) R Q)) H K :=by
  unfold cavityOuterPosteriorScore
  simp_rw [cavityOuterStieltjesPotential_first_eq_history]
  rfl

end QuantitativeFollowup
