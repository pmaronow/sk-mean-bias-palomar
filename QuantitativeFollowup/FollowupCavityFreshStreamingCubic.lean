module
public import QuantitativeFollowup.FollowupCavityPairProductBounds
public import QuantitativeFollowup.FollowupCavityChargedCrossMarkedCubic
public import QuantitativeFollowup.FollowupCavityChargedFutureMarkedCubic

@[expose] public section

/-! The signed fresh/current/future expectations are controlled by
their actual marked cubic budgets, including the current CDF factor. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFreshFresh_pairProduct_abs_le_moment
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (has : a ≤ s.m 1)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2→ObservationLeaf (trimRoot T)) :
    |cavityFreshFreshExpectation D s a T (cavityRecordedPairProduct s (trimRoot T) i l)| ≤
      cavityChargedCrossMarkedTripleMoment D s a T i l := by
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let J:=fun c d : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>∫z,
    cavityRecordedPairProduct s (trimRoot T) i l z.1*
      cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.2 d.2) z.2.1 z.2.2
        ∂anisotropicCrossVertexMarkedLaw D s a T c.2 d.2
  have he : cavityFreshFreshExpectation D s a T (cavityRecordedPairProduct s (trimRoot T) i l)=
      (cs.map (fun c=>c.1*(cs.map (fun d=>d.1*J c d)).sum)).sum := by
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
  simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
    (μ:=anisotropicCrossVertexMarkedLaw D s a T c.2 d.2) (f:=fun z=>
      cavityRecordedPairProduct s (trimRoot T) i l z.1*
        cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.2 d.2) z.2.1 z.2.2))

theorem cavityCurrentFresh_pairProduct_abs_le_moment
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (has : a ≤ s.m 1)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2→ObservationLeaf (trimRoot T)) :
    |cavityCurrentFreshExpectation D s a T (cavityRecordedPairProduct s (trimRoot T) i l)| ≤
      cavityChargedCurrentMarkedTripleMoment D s a T i l := by
  unfold cavityCurrentFreshExpectation cavityChargedCurrentMarkedTripleMoment
  apply abs_list_sum_le
  intro c hc
  have hc0:=anisotropicTrimmedVertexCharges_nonneg s a has T c hc
  have hq : (anisotropicVertexOverlap s c.2:ℝ)=cavityPhysicalCommonOverlap s (trimRoot T) c.2 c.2 := by
    rw [cavityPhysicalCommonOverlap_self]
    exact scalarSchemeTransportNode_coe s (k+2-c.2.depth) (Nat.sub_le _ _)
  rw [abs_mul,abs_mul,abs_of_nonneg hc0,abs_of_nonneg (Paper.parisiCDF_nonneg _ _),hq]
  have hh : |∫z,cavityRecordedPairProduct s (trimRoot T) i l z.1*
      cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.2 c.2) z.2.1 z.2.2
        ∂anisotropicCrossVertexMarkedLaw D s a T c.2 c.2| ≤
      ∫z,|cavityRecordedPairProduct s (trimRoot T) i l z.1*
        cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.2 c.2) z.2.1 z.2.2|
          ∂anisotropicCrossVertexMarkedLaw D s a T c.2 c.2 := by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
      (μ:=anisotropicCrossVertexMarkedLaw D s a T c.2 c.2) (f:=fun z=>
        cavityRecordedPairProduct s (trimRoot T) i l z.1*
          cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.2 c.2) z.2.1 z.2.2))
  calc
    _ ≤ c.1*1*|∫z,cavityRecordedPairProduct s (trimRoot T) i l z.1*
        cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.2 c.2) z.2.1 z.2.2
          ∂anisotropicCrossVertexMarkedLaw D s a T c.2 c.2| := by
      gcongr
      exact Paper.parisiCDF_le_one _ _
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hc0

theorem cavityFutureFresh_pairProduct_abs_le_moment
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2→ObservationLeaf (trimRoot T)) :
    |cavityFutureFreshExpectation D s a T (cavityRecordedPairProduct s (trimRoot T) i l)| ≤
      cavityChargedFutureMarkedTripleMoment D s a T i l := by
  have hi (F : Paper.Overlap→ℝ) : Integrable F (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) := by
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hq]
    exact integrable_vectorProfileFreeMeasure s a F
  unfold cavityFutureFreshExpectation cavityChargedFutureMarkedTripleMoment
  apply abs_list_sum_le
  intro c hc
  rw [abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
  apply mul_le_mul_of_nonneg_left _ (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
  calc
    _ ≤ ∫q : Paper.Overlap,‖if anisotropicVertexOverlap s c.2<q then
        (∫z,cavityRecordedPairProduct s (trimRoot T) i l z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2
          ∂anisotropicFutureVertexMarkedLaw D s a T c.2 q) else 0‖
            ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (μ:=parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) (f:=fun q : Paper.Overlap=>
          if anisotropicVertexOverlap s c.2<q then
            (∫z,cavityRecordedPairProduct s (trimRoot T) i l z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2
              ∂anisotropicFutureVertexMarkedLaw D s a T c.2 q) else 0))
    _ ≤ _ := by
      apply integral_mono (hi _) (hi _)
      intro q
      change ‖if anisotropicVertexOverlap s c.2<q then _ else 0‖≤_
      have hv : anisotropicVertexOverlap s c.2=cavityProfileLevel s c.2.depth := rfl
      rw [hv]
      split_ifs with h
      · simp only [ite_eq_left h]
        simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
          (μ:=anisotropicFutureVertexMarkedLaw D s a T c.2 q) (f:=fun z=>
            cavityRecordedPairProduct s (trimRoot T) i l z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2))
      · simp only [ite_eq_right h,norm_zero,le_refl]

end QuantitativeFollowup
