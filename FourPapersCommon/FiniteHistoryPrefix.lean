module
public import FourPapersCommon.FiniteHistory

@[expose] public section

/-! The actual restricted-law path induction only needs the finite time
prefix being claimed, and retains every previous coordinate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal
namespace FourPapersCommon
variable {State : Type*} [MeasurableSpace State]

theorem historySample_law_of_restricted_up_to {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → State) (hX : ∀ t, Measurable[F t] (X t))
    (T : ℕ → ℝ≥0) (N : ℕ) (hT : ∀ i j, i≤j → j≤N → T i≤T j)
    (κ : ℕ → Kernel State State) (hκ : ∀ n, IsMarkovKernel (κ n))
    (hlaw : ∀ n, n<N → ∀ E : Set Ω, MeasurableSet[F (T n)] E →
      (P.restrict E).map (X (T (n + 1))) = (κ n) ∘ₘ (P.restrict E).map (X (T n)))
    (n : ℕ) (hn : n≤N) :
    P.map (historySample X T n) = finiteHistoryLaw (P.map (X (T 0))) κ n := by
  have hXg (t : ℝ≥0) : Measurable (X t) := (hX t).mono (F.le t) le_rfl
  induction n with
  | zero =>
    rw [finiteHistoryLaw, Measure.map_map (by fun_prop) (hXg _)]
    congr 1
    funext sample i
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    simp only [historySample, Function.comp_def, hi, Fin.val_zero]
  | succ n ih =>
    have hnN : n≤N := by omega
    have ih := ih hnN
    haveI := hκ n
    have hY : Measurable[F (T n)] (historySample X T n) := by
      letI : MeasurableSpace Ω := F (T n)
      apply Measurable.of_eval
      intro i
      exact (hX (T i)).mono (F.mono (hT i n (show (i : ℕ) ≤ n from by omega) hnN)) le_rfl
    have hρ : Measurable (fun p : FiniteHistory State n => p (Fin.last n)) := measurable_pi_apply _
    have hj := joint_transitionLaw_of_restricted (F (T n)) P (F.le _)
      (historySample X T n) hY (X (T n)) (X (T (n + 1))) (hXg _) (hXg _)
      (fun p => p (Fin.last n)) hρ (fun _ => rfl) (κ n) (hlaw n (by omega))
    change P.map (historySample X T (n + 1)) =
      ((finiteHistoryLaw (P.map (X (T 0))) κ n) ⊗ₘ ((κ n).comap _ _)).map (historySplit n).symm
    rw [← ih, ← hj,
      Measure.map_map (historySplit n).symm.measurable
        ((measurable_historySample X hXg T n).prodMk (hXg _))]
    congr 1
    funext sample
    apply (historySplit n).injective
    simp only [MeasurableEquiv.apply_symm_apply, historySplit_apply, historySample,
      Fin.val_castSucc, Fin.val_last, Function.comp_def]
    rfl

end FourPapersCommon
