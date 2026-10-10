module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTermBudget
public import QuantitativeFollowup.SupportingGeneratedIndexedForestMomentCubic

@[expose] public section

/-! The literal three-defect estimate for a term produced by the actual
six-operation source grammar. Counts, order support and the mark budget
are derived from the path, so no desired estimate or budget is assumed.
The physical streaming factor is kept outside the normalized mark law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n C : ℕ}

theorem cavityGeneratedActualStreamingTerm_three_defects
    (hn : 0 < n) (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (S : Fin C → CavityGeneratedSiblingShape)
    {r m : ℕ} {W : CavityGeneratedConstructedForest m}
    {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualStreamingTerm μ a S r m W M)
    (c : Fin 3 → Fin W.componentCount)
    (b e : (i : Fin 3) → ObservationLeaf (W.tree (c i))) :
    (∫h, cavityGeneratedForestThreeDefectMoment D μ a W.depth W.tree
      (W.clockTemplate.clock h) c b e ∂M) ≤
      (printedGeneratedStreamingCubicConstant (cavityGeneratedStreamingInitialLeafCount S) r : ℝ) *
        cavityThirdMoment D μ a := by
  let K0 := cavityGeneratedStreamingInitialLeafCount S
  let P := printedGeneratedStreamingBudget K0 r
  have hbudget : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M
      cavityGeneratedHistoryMarks (ENNReal.ofReal (P : ℝ)) := by
    simpa only [P,K0,ENNReal.ofReal_natCast] using
      cavityGeneratedActualStreamingTerm_budget μ a ha hμ S H
  have horder := cavityGeneratedActualStreamingTerm_order μ a ha S H
  have hh := supporting_generated_indexed_forests_absolute_three_defects (I := Unit)
    hn D μ a (fun _ => M) (fun _ => W) (fun _ => c) (fun _ => b) (fun _ => e)
    (fun _ => horder) (P : ℝ) (Nat.cast_nonneg P)
    (by simpa only [Finset.univ_unique,Finset.sum_singleton] using hbudget)
  have he : (∫h, cavityGeneratedForestThreeDefectMoment D μ a W.depth W.tree
      (W.clockTemplate.clock h) c b e ∂M) ≤ (m : ℝ)*(P : ℝ)*cavityThirdMoment D μ a := by
    simpa only [Finset.univ_unique,Finset.sum_singleton] using hh
  have hm : (m : ℝ) ≤ (printedGeneratedStreamingMarkBound r : ℝ) := by
    exact_mod_cast (cavityGeneratedActualStreamingTerm_counts μ a S H).2.1
  apply he.trans
  calc
    (m : ℝ)*(P : ℝ)*cavityThirdMoment D μ a =
      (m : ℝ)*((P : ℝ)*cavityThirdMoment D μ a) := mul_assoc _ _ _
    _ ≤ (printedGeneratedStreamingMarkBound r : ℝ)*((P : ℝ)*cavityThirdMoment D μ a) :=
      mul_le_mul_of_nonneg_right hm
        (mul_nonneg (Nat.cast_nonneg P) (cavityThirdMoment_nonneg D μ a))
    _ = _ := by
      simp only [printedGeneratedStreamingCubicConstant,Nat.cast_mul,P,K0,mul_assoc]

theorem cavityGeneratedActualStreamingTerm_physical_three_defects
    (hn : 0 < n) (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (S : Fin C → CavityGeneratedSiblingShape)
    {r m : ℕ} {W : CavityGeneratedConstructedForest m}
    {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualStreamingTerm μ a S r m W M)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (c : Fin 3 → Fin W.componentCount)
    (b e : (i : Fin 3) → ObservationLeaf (W.tree (c i))) :
    (∫h, cavityGeneratedForestThreeDefectMoment
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W.depth W.tree
      (W.clockTemplate.clock h) c b e
      ∂((ENNReal.ofReal (|followupCavityAlpha n β ρ / 2|^r)) • M)) ≤
      |followupCavityAlpha n β ρ / 2|^r *
        (printedGeneratedStreamingCubicConstant (cavityGeneratedStreamingInitialLeafCount S) r : ℝ) *
          cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ u hu) μ a := by
  rw [integral_smul_measure,ENNReal.toReal_ofReal (pow_nonneg (abs_nonneg _) r)]
  change |followupCavityAlpha n β ρ / 2|^r * (∫h, _ ∂M) ≤ _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (cavityGeneratedActualStreamingTerm_three_defects hn
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a ha hμ S H c b e)
    (pow_nonneg (abs_nonneg (followupCavityAlpha n β ρ / 2)) r)

end QuantitativeFollowup
