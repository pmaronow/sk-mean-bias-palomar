module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedOriginalNormalizerTerms
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFutureSchemeIntegrals
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSchemeTerminalMoments

@[expose] public section

/-! Actual embedded vertex callbacks for coarse charge regrouping. Future
cell sums retain every upper atom and reduce to the genuine shared future law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem pad_leaf_vertex {j : ℕ} (T : FiniteTerminalGenealogy j)
    (d : ℕ) (i : ObservationLeaf T) :
    observationLeafVertex (observationTreePad T d) (observationPadLeafEmbed T d i) =
      nativeStreamingPadVertexEmbed T d (observationLeafVertex T i) := by
  induction d with
  | zero => rfl
  | succ d ih => exact congrArg FiniteCascadeRecordVertex.child ih

theorem nativeStreamingRefinementLeafEmbed_vertex (d : ℕ → ℕ)
    (T : FiniteTerminalGenealogy J) (i : ObservationLeaf T) :
    observationLeafVertex (observationRefineTree d T) (observationRefinementLeafEmbed d T i) =
      nativeStreamingRefinementVertexEmbed d T (observationLeafVertex T i) := by
  induction T with
  | leaf => rfl
  | @advance j T ih =>
      change FiniteCascadeRecordVertex.child
        (observationLeafVertex (observationTreePad (observationRefineTree d T) (d j))
          (observationPadLeafEmbed _ _ (observationRefinementLeafEmbed d T i))) = _
      rw [pad_leaf_vertex, ih]
      rfl
  | fork T U ihT ihU => cases i with
    | inl i => exact congrArg FiniteCascadeRecordVertex.left (ihT i)
    | inr i => exact congrArg FiniteCascadeRecordVertex.right (ihU i)

private theorem coarse_antitone (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hQ : Antitone Q) (hlevels : ∀j,Q (observationRefinementDepth d j)=q j) : Antitone q := by
  intro i j hij
  rw [←hlevels i,←hlevels j]
  exact hQ ((observationRefinementDepth_strictMono d).monotone hij)

theorem nativeStreamingPatternMoment_originalFresh_vertex_refinement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j,Q (observationRefinementDepth d j)=q j) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinedTerminalTest d T F)
      (.originalFresh (observationRefinementLeafEmbed d T i)
        (.vertex (nativeStreamingRefinementVertexEmbed d T v))) =
      nativeStreamingPatternMoment D μ a q T F (.originalFresh i (.vertex v)) := by
  have hq := coarse_antitone q Q d hQ hlevels
  have hQ0 : Q 0=1 := by simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  have hc : nativeStreamingOriginCommonClock Q (observationRefineTree d T)
      (.vertex (observationLeafVertex _ (observationRefinementLeafEmbed d T i)))
      (.vertex (nativeStreamingRefinementVertexEmbed d T v)) =
      nativeStreamingOriginCommonClock q T (.vertex (observationLeafVertex T i)) (.vertex v) := by
    simp only [nativeStreamingOriginCommonClock,nativeStreamingRefinementLeafEmbed_vertex,
      nativeStreamingRefinementVertexEmbed_commonPathDepth,hlevels]
  simp only [nativeStreamingPatternMoment,nativeStreamingOriginSingleProbability,
    nativeStreamingTerminalMarkMoment,hc]
  rw [nativeStreamingSingleVertexProbability_eq_law D μ a Q hQ hQ0,
    nativeStreamingSingleVertexProbability_eq_law D μ a q hq hzero]
  have H := nativeStreamingSingleVertexTerminalIntegral_refinement D μ a q Q d hQ hlevels T v
    (nativeStreamingOriginalFreshSpinTest T F i
      (nativeStreamingOriginCommonClock q T (.vertex (observationLeafVertex T i)) (.vertex v)))
  convert H using 1
  congr 1
  funext z
  simp only [nativeStreamingOriginalFreshSpinTest,nativeStreamingRefinedTerminalTest,Function.comp_apply]
  rw [show observationTerminalSpin _ (observationRefinementLeafEmbed d T i)
      (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2) =
      observationTerminalSpin T i (observationRefinementTerminalProject d T rfl
        (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2)) by
    simpa only [observationRefinementDepthLeafEmbed,observationTreeDepthCast] using
      (observationRefinementTerminalProject_leaf d T rfl i
        (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2)).symm]

theorem nativeStreamingPatternMoment_current_vertex_refinement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j,Q (observationRefinementDepth d j)=q j) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinedTerminalTest d T F)
      (.current (.vertex (nativeStreamingRefinementVertexEmbed d T v))) =
      nativeStreamingPatternMoment D μ a q T F (.current (.vertex v)) := by
  have hq := coarse_antitone q Q d hQ hlevels
  have hQ0 : Q 0=1 := by simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  simp only [nativeStreamingPatternMoment,nativeStreamingOriginCurrentProbability,
    nativeStreamingOriginLevel,nativeStreamingTerminalMarkMoment,
    nativeStreamingRefinementVertexEmbed_depth,hlevels]
  rw [nativeStreamingCurrentPairProbability_eq_law D μ a Q hQ hQ0,
    nativeStreamingCurrentPairProbability_eq_law D μ a q hq hzero]
  simpa only [nativeStreamingDefectSpinTest,nativeStreamingRefinedTerminalTest,Function.comp_apply] using
    nativeStreamingCurrentVertexTerminalIntegral_refinement D μ a q Q d hQ hlevels T v
      (nativeStreamingDefectSpinTest T F (q v.depth))

theorem nativeStreamingPatternFutureIntegral_finite_vertex
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0 ≤ a) (has : a ≤ s.m 1) (hs : s.q 1=0)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternFutureIntegral D (Paper.parisiSchemeMeasure s) a q T F (.vertex v) =
      ∫r in Ioc (q J) (q 0),if q v.depth<r then
        (∫z,nativeStreamingDefectSpinTest T F r (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
          ∂nativeStreamingFuturePairLaw D (Paper.parisiSchemeMeasure s) a q T v r) else 0
            ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
  classical
  let μ := Paper.parisiSchemeMeasure s
  let ν := parisiFreeMeasure μ a
  let g := fun r : Paper.Overlap => if q v.depth<r then
    (∫z,nativeStreamingDefectSpinTest T F r (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
      ∂nativeStreamingFuturePairLaw D μ a q T v r) else 0
  have hg : Integrable g ν := by
    dsimp only [ν,μ]
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hs]
    exact integrable_vectorProfileFreeMeasure s a g
  have hcell (j : ℕ) :
      (∫r in Ioc (q (j+1)) (q j),if q v.depth<r then
        nativeStreamingPatternMoment D μ a q T F (.future (.vertex v) j r) else 0 ∂ν)=
        ∫r in Ioc (q (j+1)) (q j),g r∂ν := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    by_cases hv : q v.depth<r
    · have hj : j<v.depth := by
        by_contra hh
        exact (not_lt_of_ge (hr.2.trans (hq (show v.depth≤j by omega)))) hv
      simp only [hv,ite_true,g,nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment]
      rw [nativeStreamingOriginFutureProbability_vertex_eq_law D μ a q hq hzero T v j hj r
        ⟨hr.1.le,hr.2⟩]
    · simp only [hv,ite_false,g]
  unfold nativeStreamingPatternFutureIntegral
  change (∑j∈Finset.range J,∫r in Ioc (q (j+1)) (q j),if q v.depth<r then
    nativeStreamingPatternMoment D μ a q T F (.future (.vertex v) j r) else 0 ∂ν)=_
  simp_rw [hcell]
  exact nativeStreaming_setIntegral_Ioc_antitone_telescope q hq ν g hg J

theorem nativeStreamingPatternFutureIntegral_finite_vertex_refinement
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0 ≤ a) (has : a ≤ s.m 1) (hs : s.q 1=0)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j,Q (observationRefinementDepth d j)=q j) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternFutureIntegral D (Paper.parisiSchemeMeasure s) a Q
      (observationRefineTree d T) (nativeStreamingRefinedTerminalTest d T F)
      (.vertex (nativeStreamingRefinementVertexEmbed d T v)) =
      nativeStreamingPatternFutureIntegral D (Paper.parisiSchemeMeasure s) a q T F (.vertex v) := by
  have hq := coarse_antitone q Q d hQ hlevels
  have hQ0 : Q 0=1 := by simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  have h00 : Q 0=q 0 := by simpa only [observationRefinementDepth] using hlevels 0
  rw [nativeStreamingPatternFutureIntegral_finite_vertex D s a ha has hs Q hQ hQ0,
    nativeStreamingPatternFutureIntegral_finite_vertex D s a ha has hs q hq hzero,hlevels J,h00]
  apply integral_congr_ae
  exact .of_forall fun r => by
    rw [nativeStreamingRefinementVertexEmbed_depth,hlevels]
    dsimp only
    split_ifs
    · simpa only [nativeStreamingDefectSpinTest,nativeStreamingRefinedTerminalTest,Function.comp_apply] using
        nativeStreamingFutureVertexTerminalIntegral_refinement D (Paper.parisiSchemeMeasure s)
          a q Q d hQ hlevels T v r (nativeStreamingDefectSpinTest T F r)
    · rfl

end QuantitativeFollowup
