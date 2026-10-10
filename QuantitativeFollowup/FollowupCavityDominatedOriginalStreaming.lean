module
public import QuantitativeFollowup.FollowupCavityDominatedPairIntegral
public import QuantitativeFollowup.FollowupCavityOriginalStreamingCubic

@[expose] public section

/-! Original-leaf terms retain their actual cubic budget after a
measurable factor of absolute value at most one is inserted. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityOriginalOriginal_dominatedPair_abs_le_moment (hn : 0 < n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1) → ℝ) (hF : Measurable F)
    (hdom : ∀r, |F r| ≤ |cavityRecordedPairProduct s (trimRoot T) i l r|) :
    |∫r, F r*cavityOriginalDistinctLeafDefect n s T r
      ∂anisotropicTrimmedRecordedTreeLaw D s a T| ≤ cavityOriginalLeafTripleMoment D s a T i l := by
  let P := anisotropicTrimmedRecordedTreeLaw D s a T
  let xs := observationLeaves (trimRoot T)
  let f := fun j h r => F r*cavityRecordedLeafPairDefect s (trimRoot T) j h r.2
  have hFb (r) : |F r| ≤ 4 := (hdom r).trans (cavityRecordedPairProduct_abs_le_four s (trimRoot T) i l r)
  have hi (j h : ObservationLeaf (trimRoot T)) : Integrable (f j h) P :=
    integrable_bounded_pair_mul_cavityDefect P F hF hFb
      _ _ ((measurable_observationLeafSpin _ j).comp measurable_snd)
      ((measurable_observationLeafSpin _ h).comp measurable_snd) _
  have he (r) : F r*cavityOriginalDistinctLeafDefect n s T r =
      (xs.map (fun j => (xs.map (fun h => f j h r)).sum)).sum := by
    rw [cavityOriginalDistinctLeafDefect_eq_leaves hn D s T r, ←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    rw [←List.sum_map_mul_left]
  simp_rw [he]
  rw [integral_list_map_sum_real P xs _ (fun j => integrable_list_map_sum_real P xs _ (hi j))]
  simp_rw [integral_list_map_sum_real P xs _ (hi _)]
  unfold cavityOriginalLeafTripleMoment
  apply abs_list_sum_le
  intro j _
  apply abs_list_sum_le
  intro h _
  exact abs_integral_cavityDominatedPair_mul_defect P s (trimRoot T) i l id measurable_id
    F hF hdom _ _ ((measurable_observationLeafSpin _ j).comp measurable_snd)
      ((measurable_observationLeafSpin _ h).comp measurable_snd) _

theorem cavityOriginalFresh_dominatedPair_abs_le_moment
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (has : a ≤ s.m 1)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1) → ℝ) (hF : Measurable F)
    (hdom : ∀r, |F r| ≤ |cavityRecordedPairProduct s (trimRoot T) i l r|) :
    |cavityOriginalFreshExpectation D s a T F| ≤ cavityChargedOriginalFreshTripleMoment D s a T i l := by
  unfold cavityOriginalFreshExpectation cavityChargedOriginalFreshTripleMoment
  apply abs_list_sum_le
  intro c hc
  rw [abs_mul, abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
  apply mul_le_mul_of_nonneg_left _ (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
  let v := c.2
  let P := anisotropicSingleVertexMarkedLaw D s a T v
  let f := fun j (z : CavityPathRecordSpace (trimRoot T) (n+1) × Configuration (n+1)) =>
    F z.1*cavitySpinOverlapDefect n
      (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v))
      (observationLeafSpin (trimRoot T) j z.1.2) z.2
  have hi (j : ObservationLeaf (trimRoot T)) : Integrable (f j) P :=
    integrable_bounded_pair_mul_cavityDefect P _ (hF.comp measurable_fst)
      (fun z => (hdom z.1).trans (cavityRecordedPairProduct_abs_le_four s (trimRoot T) i l z.1)) _ _
      ((measurable_observationLeafSpin _ j).comp (measurable_snd.comp measurable_fst)) measurable_snd _
  have he (z : CavityPathRecordSpace (trimRoot T) (n+1) × Configuration (n+1)) :
      F z.1*cavityOriginalVertexOverlapSum n s T v
        (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2) z.2 =
      ((observationLeaves (trimRoot T)).map (fun j => f j z)).sum := by
    rw [cavityOriginalVertexOverlapSum_eq_leaves, ←List.sum_map_mul_left]
  change |∫z, F z.1*cavityOriginalVertexOverlapSum n s T v
    (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2) z.2 ∂P| ≤
      ((observationLeaves (trimRoot T)).map (fun j => ∫z,
        |cavityRecordedPairProduct s (trimRoot T) i l z.1*cavitySpinOverlapDefect n
          (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v))
          (observationLeafSpin (trimRoot T) j z.1.2) z.2| ∂P)).sum
  simp_rw [he]
  rw [integral_list_map_sum_real P _ f hi]
  apply abs_list_sum_le
  intro j _
  exact abs_integral_cavityDominatedPair_mul_defect P s (trimRoot T) i l Prod.fst measurable_fst
    (F ∘ Prod.fst) (hF.comp measurable_fst) (fun z => hdom z.1) _ _
      ((measurable_observationLeafSpin _ j).comp (measurable_snd.comp measurable_fst)) measurable_snd _

end QuantitativeFollowup
