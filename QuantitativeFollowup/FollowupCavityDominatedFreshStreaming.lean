module
public import QuantitativeFollowup.FollowupCavityDominatedPairIntegral
public import QuantitativeFollowup.FollowupCavityFreshStreamingCubic

@[expose] public section

/-! Fresh, current and future marked terms retain the actual cubic
budgets for every measurable observable dominated by two defects. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFreshFresh_dominatedPair_abs_le_moment
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (has : a ≤ s.m 1)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1) → ℝ) (hF : Measurable F)
    (hdom : ∀r, |F r| ≤ |cavityRecordedPairProduct s (trimRoot T) i l r|) :
    |cavityFreshFreshExpectation D s a T F| ≤ cavityChargedCrossMarkedTripleMoment D s a T i l := by
  let cs := finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let J := fun c d : ℝ × FiniteCascadeRecordVertex (trimRoot T) => ∫z,
    F z.1*cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.2 d.2) z.2.1 z.2.2
      ∂anisotropicCrossVertexMarkedLaw D s a T c.2 d.2
  have he : cavityFreshFreshExpectation D s a T F =
      (cs.map (fun c => c.1*(cs.map (fun d => d.1*J c d)).sum)).sum := by
    unfold cavityFreshFreshExpectation
    simp_rw [←List.sum_map_mul_left]
    congr 2
    ext c
    congr 2
    ext d
    dsimp [cs,J]
    ring
  rw [he]
  unfold cavityChargedCrossMarkedTripleMoment
  apply abs_list_sum_le
  intro c hc
  rw [abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
  apply mul_le_mul_of_nonneg_left _ (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
  apply abs_list_sum_le
  intro d hd
  rw [abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T d hd)]
  apply mul_le_mul_of_nonneg_left _ (anisotropicTrimmedVertexCharges_nonneg s a has T d hd)
  have hh := abs_integral_cavityDominatedPair_mul_defect
    (anisotropicCrossVertexMarkedLaw D s a T c.2 d.2) s (trimRoot T) i l Prod.fst measurable_fst
    (F ∘ Prod.fst) (hF.comp measurable_fst) (fun z => hdom z.1)
    (fun z => z.2.1) (fun z => z.2.2) (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd)
    (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) c.2 d.2))
  simpa only [J,cavityPhysicalCommonOverlap_eq_profileLevel,Function.comp_def] using hh

theorem cavityCurrentFresh_dominatedPair_abs_le_moment
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (has : a ≤ s.m 1)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1) → ℝ) (hF : Measurable F)
    (hdom : ∀r, |F r| ≤ |cavityRecordedPairProduct s (trimRoot T) i l r|) :
    |cavityCurrentFreshExpectation D s a T F| ≤ cavityChargedCurrentMarkedTripleMoment D s a T i l := by
  unfold cavityCurrentFreshExpectation cavityChargedCurrentMarkedTripleMoment
  apply abs_list_sum_le
  intro c hc
  have hc0 := anisotropicTrimmedVertexCharges_nonneg s a has T c hc
  have hq : (anisotropicVertexOverlap s c.2 : ℝ) = cavityPhysicalCommonOverlap s (trimRoot T) c.2 c.2 := by
    rw [cavityPhysicalCommonOverlap_self]
    exact scalarSchemeTransportNode_coe s (k+2-c.2.depth) (Nat.sub_le _ _)
  rw [abs_mul,abs_mul,abs_of_nonneg hc0,abs_of_nonneg (Paper.parisiCDF_nonneg _ _),hq]
  have hh := abs_integral_cavityDominatedPair_mul_defect
    (anisotropicCrossVertexMarkedLaw D s a T c.2 c.2) s (trimRoot T) i l Prod.fst measurable_fst
    (F ∘ Prod.fst) (hF.comp measurable_fst) (fun z => hdom z.1)
    (fun z => z.2.1) (fun z => z.2.2) (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd) (cavityProfileLevel s c.2.depth)
  have hs : (cavityProfileLevel s c.2.depth : ℝ) = cavityPhysicalCommonOverlap s (trimRoot T) c.2 c.2 := by
    rw [cavityPhysicalCommonOverlap_self]
    exact cavityProfileLevel_coe_for_streaming s c.2.depth
  simp_rw [hs] at hh
  calc
    _ ≤ c.1*1*|∫z, F z.1*cavitySpinOverlapDefect n
        (cavityPhysicalCommonOverlap s (trimRoot T) c.2 c.2) z.2.1 z.2.2
          ∂anisotropicCrossVertexMarkedLaw D s a T c.2 c.2| := by
      gcongr
      exact Paper.parisiCDF_le_one _ _
    _ ≤ _ := by simpa only [mul_one,Function.comp_def] using mul_le_mul_of_nonneg_left hh hc0

theorem cavityFutureFresh_dominatedPair_abs_le_moment
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1) → ℝ) (hF : Measurable F)
    (hdom : ∀r, |F r| ≤ |cavityRecordedPairProduct s (trimRoot T) i l r|) :
    |cavityFutureFreshExpectation D s a T F| ≤ cavityChargedFutureMarkedTripleMoment D s a T i l := by
  have hi (G : Paper.Overlap → ℝ) : Integrable G (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) := by
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hq]
    exact integrable_vectorProfileFreeMeasure s a G
  unfold cavityFutureFreshExpectation cavityChargedFutureMarkedTripleMoment
  apply abs_list_sum_le
  intro c hc
  rw [abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
  apply mul_le_mul_of_nonneg_left _ (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
  calc
    _ ≤ ∫q : Paper.Overlap,‖if anisotropicVertexOverlap s c.2 < q then
        (∫z, F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2
          ∂anisotropicFutureVertexMarkedLaw D s a T c.2 q) else 0‖
            ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (μ := parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) (f := fun q : Paper.Overlap =>
          if anisotropicVertexOverlap s c.2 < q then
            (∫z, F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2
              ∂anisotropicFutureVertexMarkedLaw D s a T c.2 q) else 0))
    _ ≤ _ := by
      apply integral_mono (hi _) (hi _)
      intro q
      change ‖if anisotropicVertexOverlap s c.2 < q then _ else 0‖ ≤ _
      have hv : anisotropicVertexOverlap s c.2 = cavityProfileLevel s c.2.depth := rfl
      rw [hv]
      split_ifs with h
      · simp only [ite_eq_left h,Real.norm_eq_abs]
        exact abs_integral_cavityDominatedPair_mul_defect
          (anisotropicFutureVertexMarkedLaw D s a T c.2 q) s (trimRoot T) i l Prod.fst measurable_fst
          (F ∘ Prod.fst) (hF.comp measurable_fst) (fun z => hdom z.1)
          (fun z => z.2.1) (fun z => z.2.2) (measurable_fst.comp measurable_snd)
          (measurable_snd.comp measurable_snd) q
      · simp only [ite_eq_right h,norm_zero,le_refl]

end QuantitativeFollowup
