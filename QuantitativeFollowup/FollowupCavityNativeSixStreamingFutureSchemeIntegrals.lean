module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFutureSchemeMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket

@[expose] public section

/-! The finite strict-future expectation is the actual halfclosed-cell
native future expression. Repeated nodes contribute empty cells, while
every upper atom remains in exactly its physical observation cell. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreaming_setIntegral_Ioc_antitone_telescope
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (μ : Measure Paper.Overlap)
    (f : Paper.Overlap → ℝ) (hf : Integrable f μ) (J : ℕ) :
    (∑j∈Finset.range J,∫r in Ioc (q (j+1)) (q j),f r∂μ)=
      ∫r in Ioc (q J) (q 0),f r∂μ := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ,ih,add_comm,
        ←setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
          hf.integrableOn hf.integrableOn,
        Ioc_union_Ioc_eq_Ioc (hq (Nat.le_succ J)) (hq (Nat.zero_le J))]

theorem nativeStreamingPatternFutureIntegral_scheme_vertex
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternFutureIntegral D (Paper.parisiSchemeMeasure s) a
      (anisotropicRecordedSchemeSchedule s) T F (.vertex v) =
      ∫r,if anisotropicVertexOverlap s (T:=T.advance) v<r then
        (∫z,F (finiteCascadeRecordTerminalSpins T z.1.2)*
          cavitySpinOverlapDefect n r z.2.1 z.2.2
            ∂anisotropicFutureVertexMarkedLaw D s a T.advance v r) else 0
              ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
  classical
  let q := anisotropicRecordedSchemeSchedule s
  let μ := parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  let g := fun r : Paper.Overlap=>if q v.depth<r then
    (∫z,F (finiteCascadeRecordTerminalSpins T z.1.2)*
      cavitySpinOverlapDefect n r z.2.1 z.2.2
        ∂anisotropicFutureVertexMarkedLaw D s a T.advance v r) else 0
  have hqv : q v.depth=anisotropicVertexOverlap s (T:=T.advance) v :=
    nativeStreamingSchemeSchedule_eq_profileLevel s v.depth
  have hg : Integrable g μ := by
    dsimp only [μ]
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hq]
    exact integrable_vectorProfileFreeMeasure s a g
  have hAE := nativeStreamingFutureLawTerminalMoment_scheme_trimmed_ae D s a ha has hq T v
    (fun r=>nativeStreamingDefectSpinTest T F r)
  have hcell (j : ℕ) :
      (∫r in Ioc (q (j+1)) (q j),if q v.depth<r then
        nativeStreamingPatternMoment D (Paper.parisiSchemeMeasure s) a q T F
          (.future (.vertex v) j r) else 0 ∂μ)=
        ∫r in Ioc (q (j+1)) (q j),g r∂μ := by
    apply integral_congr_ae
    filter_upwards [hAE.filter_mono ae_restrict_le,
      ae_restrict_mem measurableSet_Ioc] with r hr hmem
    by_cases hfuture : q v.depth<r
    · have hj : j<v.depth := by
        by_contra hh
        have hle := anisotropicRecordedSchemeSchedule_antitone s (show v.depth≤j by omega)
        exact (not_lt_of_ge (hmem.2.trans hle)) hfuture
      simp only [hfuture,ite_true,g]
      simp only [nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment]
      rw [nativeStreamingOriginFutureProbability_vertex_eq_law D _ a q
        (anisotropicRecordedSchemeSchedule_antitone s) (nativeStreamingSchemeSchedule_zero s)
        T v j hj r ⟨hmem.1.le,hmem.2⟩]
      simpa only [nativeStreamingDefectSpinTest] using
        hr (by simpa only [q,nativeStreamingSchemeSchedule_eq_profileLevel] using hfuture)
    · simp only [hfuture,ite_false,g]
  unfold nativeStreamingPatternFutureIntegral
  change (∑j∈Finset.range (k+1),∫r in Ioc (q (j+1)) (q j),if q v.depth<r then
    nativeStreamingPatternMoment D (Paper.parisiSchemeMeasure s) a q T F
      (.future (.vertex v) j r) else 0 ∂μ)=_
  simp_rw [hcell]
  rw [nativeStreaming_setIntegral_Ioc_antitone_telescope q
    (anisotropicRecordedSchemeSchedule_antitone s) μ g hg]
  have hlast : q (k+1)=zeroOverlap := by
    apply Subtype.ext
    change (anisotropicRecordedSchemeSchedule s (k+1):ℝ)=0
    rw [nativeStreamingSchemeSchedule_eq_profileLevel,cavityProfileLevel_coe_for_streaming]
    simpa using hq
  have hfirst : q 0=1 := nativeStreamingSchemeSchedule_zero s
  rw [hlast,hfirst]
  have hzero : g zeroOverlap=0 := by
    simp only [g]
    exact if_neg (not_lt_of_ge (show zeroOverlap≤q v.depth from bot_le))
  calc
    (∫r in Ioc zeroOverlap 1,g r∂μ)=∫r,g r∂μ := by
      rw [←integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      exact .of_forall fun r=>by
        by_cases hr : r=zeroOverlap
        · subst r
          rw [Set.indicator_of_notMem (show zeroOverlap∉Ioc zeroOverlap (1:Paper.Overlap) by
            exact fun hh=>lt_irrefl _ hh.1),hzero]
        · rw [Set.indicator_of_mem (show r∈Ioc zeroOverlap (1:Paper.Overlap) from
            ⟨lt_of_le_of_ne bot_le (Ne.symm hr),le_top⟩)]
    _ = _ := by simp only [g,hqv,μ]

theorem cavityFutureFreshExpectation_eq_native_vertex_patterns
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    cavityFutureFreshExpectation D s a T.advance
      (fun z=>F (finiteCascadeRecordTerminalSpins T z.2)) =
      nativeStreamingVertexChargeSum (anisotropicSchemeMass s) a T
        (fun v=>nativeStreamingPatternFutureIntegral D (Paper.parisiSchemeMeasure s) a
          (anisotropicRecordedSchemeSchedule s) T F (.vertex v)) := by
  unfold cavityFutureFreshExpectation nativeStreamingVertexChargeSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  dsimp only
  rw [nativeStreamingPatternFutureIntegral_scheme_vertex D s a ha has hq T F c.2]

end QuantitativeFollowup
