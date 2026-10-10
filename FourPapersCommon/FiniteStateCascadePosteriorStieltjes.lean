module
public import FourPapersCommon.FiniteStateCascadePosteriorExpectation
public import QuantitativePaper.VectorTailScoreBounds

@[expose] public section

/-! Positive Stieltjes weights of total one in the genuine finite-state
posterior score. They give bounds independent of the number of cells. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT QuantitativePaper
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1400000

def cascadePosteriorStieltjesWeight (a : ℕ→ℝ) (N : ℕ) : Option (Option (Fin N))→ℝ
  | none=>1-a 0
  | some none=>a N
  | some (some i)=>a (N-(i+1))-a (N-i)

def cascadePosteriorStieltjesPotential (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ) (z : Fin (N+1)→Field n) :
    Option (Option (Fin N))→FiniteStateField S→ℝ
  | none=>fun H=>cascadePosteriorHistoryPotential V a L (N+1) (N+1) H z
  | some none=>fun H=>cascadePosteriorHistoryPotential V a L (N+1) 0 H z
  | some (some i)=>fun H=>cascadePosteriorHistoryPotential V a L (N+1) (i+1) H z

theorem cascadePosteriorStieltjesWeight_nonneg (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (ha1 : a 0≤1) (hdec : Antitone a) (N : ℕ) (i : Option (Option (Fin N))) :
    0≤cascadePosteriorStieltjesWeight a N i := by
  cases i with
  | none=>exact sub_nonneg.mpr ha1
  | some i=>
    cases i with
    | none=>exact ha N
    | some i=>exact sub_nonneg.mpr (hdec (by omega))

theorem cascadePosteriorStieltjesWeight_sum (a : ℕ→ℝ) (N : ℕ) :
    (∑i,cascadePosteriorStieltjesWeight a N i)=1 := by
  rw [Fintype.sum_option,Fintype.sum_option]
  simp only [cascadePosteriorStieltjesWeight]
  rw [Fin.sum_univ_eq_sum_range (fun i=>a (N-(i+1))-a (N-i)) N,
    Finset.sum_range_sub (fun i=>a (N-i)) N]
  simp

theorem cascadePosteriorLogDensity_stieltjes (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ)
    (H : FiniteStateField S) (z : (Fin (N+1)→Field n)×S) :
    cascadePosteriorLogDensity V a L (N+1) H z=
      V z.2+(cascadePosteriorHistory L (N+1) H z.1 (Fin.last (N+1))) z.2-
        ∑i,cascadePosteriorStieltjesWeight a N i*
          cascadePosteriorStieltjesPotential V a L N z.1 i H := by
  rw [cascadePosteriorLogDensity,Fintype.sum_option,Fintype.sum_option]
  simp only [cascadePosteriorStieltjesWeight,cascadePosteriorStieltjesPotential]
  simp only [Nat.add_sub_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun i=>a (N-i)*
    (cascadePosteriorHistoryPotential V a L (N+1) (i+1) H z.1-
      cascadePosteriorHistoryPotential V a L (N+1) i H z.1)) (N+1)]
  rw [weighted_difference_sum (fun i=>a (N-i))
    (fun i=>cascadePosteriorHistoryPotential V a L (N+1) i H z.1) N]
  rw [Fin.sum_univ_eq_sum_range (fun i=>(a (N-(i+1))-a (N-i))*
    cascadePosteriorHistoryPotential V a L (N+1) (i+1) H z.1) N]
  simp only [Nat.sub_self,Nat.sub_zero,Nat.add_comm]
  ring

theorem cascadePosteriorHistoryPotential_eq_translate (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (z : Fin j→Field n) :
    (fun H=>cascadePosteriorHistoryPotential V a L j i H z)=
      fun H=>finiteStateGaussianTerminalCascade V a L (j-i)
        (H+cascadePosteriorHistory L j 0 z (Fin.ofNat (j+1) i)) := by
  funext H
  unfold cascadePosteriorHistoryPotential historyExtended
  rw [cascadePosteriorHistory_eq_initial_add]

theorem norm_cascadePosteriorLogDensity_jet_le (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (r : ℕ) (A B : ℝ) (hB : 0≤B)
    (hU : ∀j H,‖iteratedFDeriv ℝ r (finiteStateGaussianTerminalCascade V a L j) H‖≤B)
    (hT : ∀w H σ,‖iteratedFDeriv ℝ r (fun Q : FiniteStateField S=>V σ+(Q+w) σ) H‖≤A)
    (j : ℕ) (H : FiniteStateField S) (z : (Fin j→Field n)×S) :
    ‖iteratedFDeriv ℝ r (fun Q=>cascadePosteriorLogDensity V a L j Q z) H‖≤A+B := by
  cases j with
  | zero=>
    have he : (fun Q=>cascadePosteriorLogDensity V a L 0 Q z)=
        fun Q=>V z.2+(Q+0) z.2-finiteStateGaussianTerminalCascade V a L 0 Q := by
      funext Q
      simp [cascadePosteriorLogDensity,cascadePosteriorHistoryPotential,cascadePosteriorHistory,
        independentHistory,historyExtended]
    rw [he]
    have hTs : ContDiff ℝ ∞ (fun Q : FiniteStateField S=>V z.2+(Q+0) z.2) := by fun_prop
    change ‖iteratedFDeriv ℝ r ((fun Q : FiniteStateField S=>V z.2+(Q+0) z.2)-
      finiteStateGaussianTerminalCascade V a L 0) H‖≤A+B
    rw [iteratedFDeriv_sub_apply (i:=r) (hTs.of_le (by simp)).contDiffAt
      ((contDiff_finiteStateGaussianTerminalCascade V a ha L 0).of_le (by simp)).contDiffAt]
    exact (norm_sub_le _ _).trans (add_le_add (hT 0 H z.2) (hU 0 H))
  | succ N=>
    let w := cascadePosteriorHistory L (N+1) 0 z.1 (Fin.last (N+1))
    let U := cascadePosteriorStieltjesPotential V a L N z.1
    have hs (i : Option (Option (Fin N))) : ContDiff ℝ ∞ (U i) := by
      cases i with
      | none=>
        dsimp only [U,cascadePosteriorStieltjesPotential]
        rw [cascadePosteriorHistoryPotential_eq_translate]
        exact (contDiff_finiteStateGaussianTerminalCascade V a ha L _).comp (contDiff_id.add contDiff_const)
      | some i=>
        cases i <;> dsimp only [U,cascadePosteriorStieltjesPotential] <;>
          rw [cascadePosteriorHistoryPotential_eq_translate] <;>
          exact (contDiff_finiteStateGaussianTerminalCascade V a ha L _).comp (contDiff_id.add contDiff_const)
    have hb (i : Option (Option (Fin N))) (Q : FiniteStateField S) :
        ‖iteratedFDeriv ℝ r (U i) Q‖≤B := by
      cases i with
      | none=>
        dsimp only [U,cascadePosteriorStieltjesPotential]
        rw [cascadePosteriorHistoryPotential_eq_translate,iteratedFDeriv_comp_add_right]
        exact hU _ _
      | some i=>
        cases i <;> dsimp only [U,cascadePosteriorStieltjesPotential] <;>
          rw [cascadePosteriorHistoryPotential_eq_translate,iteratedFDeriv_comp_add_right] <;> exact hU _ _
    have hsum := norm_iteratedFDeriv_convex_sum_le Finset.univ (cascadePosteriorStieltjesWeight a N)
      U r B hB (fun i _=>cascadePosteriorStieltjesWeight_nonneg a ha ha1 hdec N i)
      (cascadePosteriorStieltjesWeight_sum a N).le (fun i _=>hs i) (fun i _=>hb i) H
    have hTs : ContDiff ℝ ∞ (fun Q : FiniteStateField S=>V z.2+(Q+w) z.2) := by fun_prop
    have hUs : ContDiff ℝ ∞ (fun Q=>∑i,cascadePosteriorStieltjesWeight a N i*U i Q) :=
      ContDiff.sum fun i _=>contDiff_const.mul (hs i)
    have he : (fun Q=>cascadePosteriorLogDensity V a L (N+1) Q z)=
        fun Q=>V z.2+(Q+w) z.2-∑i,cascadePosteriorStieltjesWeight a N i*U i Q := by
      funext Q
      rw [cascadePosteriorLogDensity_stieltjes,cascadePosteriorHistory_eq_initial_add]
    rw [he]
    change ‖iteratedFDeriv ℝ r ((fun Q : FiniteStateField S=>V z.2+(Q+w) z.2)-
      (fun Q=>∑i,cascadePosteriorStieltjesWeight a N i*U i Q)) H‖≤A+B
    rw [iteratedFDeriv_sub_apply (i:=r) (hTs.of_le (by simp)).contDiffAt
      (hUs.of_le (by simp)).contDiffAt]
    exact (norm_sub_le _ _).trans (add_le_add (hT w H z.2) hsum)

end FourPapersCommon
