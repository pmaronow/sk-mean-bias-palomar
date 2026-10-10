module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterLaw
public import QuantitativeFollowup.FollowupCavityCppZeroResponseSecondScore
public import QuantitativePaper.VectorHistoryProperties

@[expose] public section

/-! Exact free Stieltjes charges of the actual fractional-tilted outer
posterior. Its root charge is the original root mass minus the outer mass. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityOuterStieltjesWeight (a : ℕ→ℝ) (s : ℝ) (N : ℕ) : Option (Option (Fin N))→ℝ
  | none=>1-a 0
  | some none=>a N-s
  | some (some i)=>a (N-(i+1))-a (N-i)

theorem cavityOuterStieltjesWeight_nonneg (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (ha1 : a 0≤1) (hdec : Antitone a) (s : ℝ) (N : ℕ) (hs : s≤a N)
    (i : Option (Option (Fin N))) : 0≤cavityOuterStieltjesWeight a s N i :=by
  cases i with
  | none=>exact sub_nonneg.mpr ha1
  | some i=>cases i with
    | none=>exact sub_nonneg.mpr hs
    | some i=>exact sub_nonneg.mpr (hdec (by omega))

theorem cavityOuterStieltjesWeight_sum (a : ℕ→ℝ) (s : ℝ) (N : ℕ) :
    (∑i,cavityOuterStieltjesWeight a s N i)=1-s :=by
  have ht:=cascadePosteriorStieltjesWeight_sum a N
  rw [Fintype.sum_option,Fintype.sum_option] at ht ⊢
  simp only [cavityOuterStieltjesWeight,cascadePosteriorStieltjesWeight] at ht ⊢
  linarith

private theorem cavityPosteriorRootPotential (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ)
    (z : Fin (N+1)→Field n) (H : FiniteStateField S) :
    cascadePosteriorStieltjesPotential V a L N z (some none) H=
      finiteStateGaussianTerminalCascade V a L (N+1) H :=by
  simp [cascadePosteriorStieltjesPotential,cascadePosteriorHistoryPotential,
    historyExtended,cascadePosteriorHistory,independentHistory_initial]

theorem cavityOuterPosteriorLogDensity_stieltjes (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (p : FiniteStateGaussianInput J×((Fin (N+1)→Field n)×S)) :
    cavityOuterPosteriorLogDensity V a L s (N+1) R H p=
      V p.2.2+(cascadePosteriorHistory L (N+1) (H+R p.1) p.2.1 (Fin.last (N+1))) p.2.2-
        ∑i,cavityOuterStieltjesWeight a s N i*
          cascadePosteriorStieltjesPotential V a L N p.2.1 i (H+R p.1)-
        Real.log (cavityOuterPosteriorNormalizer V a L s (N+1) R H) :=by
  rw [cavityOuterPosteriorLogDensity,cascadePosteriorLogDensity_stieltjes,
    Fintype.sum_option,Fintype.sum_option,Fintype.sum_option,Fintype.sum_option]
  simp only [cavityOuterStieltjesWeight,cascadePosteriorStieltjesWeight,cavityPosteriorRootPotential]
  ring

end QuantitativeFollowup
