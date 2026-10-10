module
public import QuantitativeFollowup.FollowupCavityPairProductBounds
public import QuantitativeFollowup.FollowupCavityOriginalMarkedCubic
public import QuantitativeFollowup.FollowupCavityChargedOriginalFreshCubic

@[expose] public section

/-! Absolute expectations of the actual signed original-leaf streaming
terms are bounded by the literal third moments of their marked laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityOriginalVertexOverlapSum_eq_leaves (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) (τ : Configuration (n+1)) :
    cavityOriginalVertexOverlapSum n s T v (finiteCascadeRecordTerminalSpins (trimRoot T) r.2) τ =
      ((observationLeaves (trimRoot T)).map (fun j=>cavitySpinOverlapDefect n
        (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v))
        (observationLeafSpin (trimRoot T) j r.2) τ)).sum := by
  unfold cavityOriginalVertexOverlapSum
  rw [finiteCascadeTerminalVertices_eq_observationLeaves]
  simp only [List.map_map,Function.comp_def,cavityPhysicalCommonOverlap_eq_profileLevel]

theorem cavityOriginalDistinctLeafDefect_eq_leaves (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (T : FiniteTerminalGenealogy (k+2))
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    cavityOriginalDistinctLeafDefect n s T r =
      ((observationLeaves (trimRoot T)).map (fun j=>((observationLeaves (trimRoot T)).map
        (fun h=>cavityRecordedLeafPairDefect s (trimRoot T) j h r.2)).sum)).sum := by
  rw [←cavityRecordedOriginalOriginalDefect_eq_distinct_leaves D hn s T (D.variance (Fin.last n)) r]
  unfold cavityRecordedOriginalOriginalDefect
  rw [finiteCascadeTerminalVertices_eq_observationLeaves]
  simp only [List.map_map,Function.comp_def,cavityRecordedMarkPairDefect_originals,
    cavityPhysicalCommonOverlap_eq_profileLevel,observationLeaf_commonPathDepth,cavityRecordedLeafPairDefect]

theorem cavityOriginalOriginal_pairProduct_abs_le_moment (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2→ObservationLeaf (trimRoot T)) :
    |∫r,cavityRecordedPairProduct s (trimRoot T) i l r*cavityOriginalDistinctLeafDefect n s T r
      ∂anisotropicTrimmedRecordedTreeLaw D s a T| ≤ cavityOriginalLeafTripleMoment D s a T i l := by
  let P := anisotropicTrimmedRecordedTreeLaw D s a T
  let xs := observationLeaves (trimRoot T)
  let f := fun j h r => cavityRecordedPairProduct (n:=n) s (trimRoot T) i l r *
    cavityRecordedLeafPairDefect s (trimRoot T) j h r.2
  have hi (j h : ObservationLeaf (trimRoot T)) : Integrable (f j h) P :=
    integrable_bounded_pair_mul_cavityDefect P _ (measurable_cavityRecordedPairProduct s (trimRoot T) i l)
      (cavityRecordedPairProduct_abs_le_four s (trimRoot T) i l)
      _ _ ((measurable_observationLeafSpin _ j).comp measurable_snd)
      ((measurable_observationLeafSpin _ h).comp measurable_snd) _
  have he (r) : cavityRecordedPairProduct s (trimRoot T) i l r*cavityOriginalDistinctLeafDefect n s T r =
      (xs.map (fun j=>(xs.map (fun h=>f j h r)).sum)).sum := by
    rw [cavityOriginalDistinctLeafDefect_eq_leaves hn D s T r,←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    rw [←List.sum_map_mul_left]
  simp_rw [he]
  rw [integral_list_map_sum_real P xs _ (fun j=>integrable_list_map_sum_real P xs _ (hi j))]
  simp_rw [integral_list_map_sum_real P xs _ (hi _)]
  unfold cavityOriginalLeafTripleMoment
  apply abs_list_sum_le
  intro j _
  apply abs_list_sum_le
  intro h _
  simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ:=P) (f:=f j h))

theorem cavityOriginalFresh_pairProduct_abs_le_moment
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (has : a ≤ s.m 1)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2→ObservationLeaf (trimRoot T)) :
    |cavityOriginalFreshExpectation D s a T (cavityRecordedPairProduct s (trimRoot T) i l)| ≤
      cavityChargedOriginalFreshTripleMoment D s a T i l := by
  unfold cavityOriginalFreshExpectation cavityChargedOriginalFreshTripleMoment
  apply abs_list_sum_le
  intro c hc
  rw [abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
  apply mul_le_mul_of_nonneg_left _ (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
  let v := c.2
  let P := anisotropicSingleVertexMarkedLaw D s a T v
  let f := fun j (z : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)) =>
    cavityRecordedPairProduct s (trimRoot T) i l z.1*cavitySpinOverlapDefect n
      (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v))
      (observationLeafSpin (trimRoot T) j z.1.2) z.2
  have hi (j : ObservationLeaf (trimRoot T)) : Integrable (f j) P :=
    integrable_bounded_pair_mul_cavityDefect P _
      ((measurable_cavityRecordedPairProduct s (trimRoot T) i l).comp measurable_fst)
      (fun z=>cavityRecordedPairProduct_abs_le_four s (trimRoot T) i l z.1) _ _
      ((measurable_observationLeafSpin _ j).comp (measurable_snd.comp measurable_fst)) measurable_snd _
  have he (z : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)) :
      cavityRecordedPairProduct s (trimRoot T) i l z.1*cavityOriginalVertexOverlapSum n s T v
        (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2) z.2 =
      ((observationLeaves (trimRoot T)).map (fun j=>f j z)).sum := by
    rw [cavityOriginalVertexOverlapSum_eq_leaves,←List.sum_map_mul_left]
  change |∫z,cavityRecordedPairProduct s (trimRoot T) i l z.1*cavityOriginalVertexOverlapSum n s T v
    (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2) z.2 ∂P|≤
      ((observationLeaves (trimRoot T)).map (fun j=>∫z,|f j z|∂P)).sum
  simp_rw [he]
  rw [integral_list_map_sum_real P _ f hi]
  apply abs_list_sum_le
  intro j _
  simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ:=P) (f:=f j))

end QuantitativeFollowup
