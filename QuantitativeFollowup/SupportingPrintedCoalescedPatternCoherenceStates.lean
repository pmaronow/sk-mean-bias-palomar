module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeEndpointCoherenceLaws
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternVertexCoherenceCrossOrigin

@[expose] public section

/-! Zero-time coherence at every original edge, with the entire original
record retained.  All fresh-spin probabilities are the actual graft laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def nativeCoalescedOriginValid (q : ℕ → Paper.Overlap)
    {T : FiniteTerminalGenealogy J} : NativeStreamingOrigin T → Prop
  | .vertex _ => True
  | .edge e r => r ∈ Icc (q (e.depth+1)) (q e.depth)

theorem nativeStreamingRecordedLaw_edge_same_time_coherent
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (he : q (e.depth+1)=q e.depth) :
    ∀ᵐ z ∂anisotropicRecordedProfileTreeLaw D μ a q T,
      nativeStreamingVertexState (nativeStreamingEdgeParentVertex e) z.1 z.2 =
        nativeStreamingVertexState (nativeStreamingEdgeChildVertex e) z.1 z.2 := by
  exact Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
      (nativeStreamingVertexState_measurable _))
    (.of_forall (nativeStreamingRecordedKernel_edge_same_time_coherent D μ q e he))

theorem nativeStreamingSingleVertexKernel_eq_of_clock_state
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex T) (hc : q v.depth=q w.depth)
    (hs : ∀ᵐ z ∂anisotropicRecordedProfileTreeLaw D μ a q T,
      nativeStreamingVertexState v z.1 z.2=nativeStreamingVertexState w z.1 z.2) :
    nativeStreamingSingleVertexKernel D μ q T v =ᵐ[
      anisotropicRecordedProfileTreeLaw D μ a q T]
        nativeStreamingSingleVertexKernel D μ q T w := by
  filter_upwards [hs] with z hz
  change anisotropicObservationTerminalSpinKernel D μ (q v.depth)
      (nativeStreamingVertexState v z.1 z.2) =
    anisotropicObservationTerminalSpinKernel D μ (q w.depth)
      (nativeStreamingVertexState w z.1 z.2)
  rw [hc,hz]

theorem nativeStreamingSingleVertexProbability_eq_of_clock_state
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (v w : FiniteCascadeRecordVertex T)
    (hc : q v.depth=q w.depth)
    (hs : ∀ᵐ z ∂anisotropicRecordedProfileTreeLaw D μ a q T,
      nativeStreamingVertexState v z.1 z.2=nativeStreamingVertexState w z.1 z.2) :
    nativeStreamingSingleVertexProbability D μ a q T v =
      nativeStreamingSingleVertexProbability D μ a q T w := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [nativeStreamingSingleVertexProbability_eq_law D μ a q hq hzero T v,
    nativeStreamingSingleVertexProbability_eq_law D μ a q hq hzero T w]
  exact Measure.compProd_congr
    (nativeStreamingSingleVertexKernel_eq_of_clock_state D μ a q T v w hc hs)

theorem nativeStreamingCurrentPairProbability_eq_of_clock_state
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (v w : FiniteCascadeRecordVertex T)
    (hc : q v.depth=q w.depth)
    (hs : ∀ᵐ z ∂anisotropicRecordedProfileTreeLaw D μ a q T,
      nativeStreamingVertexState v z.1 z.2=nativeStreamingVertexState w z.1 z.2) :
    nativeStreamingCurrentPairProbability D μ a q T v =
      nativeStreamingCurrentPairProbability D μ a q T w := by
  have hk : nativeStreamingCurrentPairKernel D μ q T v =ᵐ[
      anisotropicRecordedProfileTreeLaw D μ a q T]
        nativeStreamingCurrentPairKernel D μ q T w := by
    filter_upwards [hs] with z hz
    change (anisotropicObservationTerminalSpinKernel D μ (q v.depth) ×ₖ
      anisotropicObservationTerminalSpinKernel D μ (q v.depth))
        (nativeStreamingVertexState v z.1 z.2) =
      (anisotropicObservationTerminalSpinKernel D μ (q w.depth) ×ₖ
        anisotropicObservationTerminalSpinKernel D μ (q w.depth))
          (nativeStreamingVertexState w z.1 z.2)
    rw [hc,hz]
  apply ProbabilityMeasure.toMeasure_injective
  rw [nativeStreamingCurrentPairProbability_eq_law D μ a q hq hzero T v,
    nativeStreamingCurrentPairProbability_eq_law D μ a q hq hzero T w]
  exact Measure.compProd_congr hk

theorem nativeStreamingCrossVertexProbability_left_eq_of_clock_state
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (v w z : FiniteCascadeRecordVertex T)
    (hc : q v.depth=q w.depth)
    (hs : ∀ᵐ x ∂anisotropicRecordedProfileTreeLaw D μ a q T,
      nativeStreamingVertexState v x.1 x.2=nativeStreamingVertexState w x.1 x.2) :
    nativeStreamingCrossVertexProbability D μ a q T v z =
      nativeStreamingCrossVertexProbability D μ a q T w z := by
  have hk := nativeStreamingSingleVertexKernel_eq_of_clock_state D μ a q T v w hc hs
  apply ProbabilityMeasure.toMeasure_injective
  rw [nativeStreamingCrossVertexProbability_eq_law D μ a q hq hzero T v z,
    nativeStreamingCrossVertexProbability_eq_law D μ a q hq hzero T w z]
  apply Measure.compProd_congr
  filter_upwards [hk] with x hx
  change (nativeStreamingSingleVertexKernel D μ q T v ×ₖ
      nativeStreamingSingleVertexKernel D μ q T z) x =
    (nativeStreamingSingleVertexKernel D μ q T w ×ₖ
      nativeStreamingSingleVertexKernel D μ q T z) x
  simp only [Kernel.prod_apply,hx]

theorem nativeStreamingCrossVertexProbability_right_eq_of_clock_state
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (v w z : FiniteCascadeRecordVertex T)
    (hc : q v.depth=q w.depth)
    (hs : ∀ᵐ x ∂anisotropicRecordedProfileTreeLaw D μ a q T,
      nativeStreamingVertexState v x.1 x.2=nativeStreamingVertexState w x.1 x.2) :
    nativeStreamingCrossVertexProbability D μ a q T z v =
      nativeStreamingCrossVertexProbability D μ a q T z w := by
  have hk := nativeStreamingSingleVertexKernel_eq_of_clock_state D μ a q T v w hc hs
  apply ProbabilityMeasure.toMeasure_injective
  rw [nativeStreamingCrossVertexProbability_eq_law D μ a q hq hzero T z v,
    nativeStreamingCrossVertexProbability_eq_law D μ a q hq hzero T z w]
  apply Measure.compProd_congr
  filter_upwards [hk] with x hx
  change (nativeStreamingSingleVertexKernel D μ q T z ×ₖ
      nativeStreamingSingleVertexKernel D μ q T v) x =
    (nativeStreamingSingleVertexKernel D μ q T z ×ₖ
      nativeStreamingSingleVertexKernel D μ q T w) x
  simp only [Kernel.prod_apply,hx]

theorem nativeStreamingCoalesced_commonPath_symm {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v w : FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth T v w = finiteCascadeCommonPathDepth T w v := by
  induction T with
  | leaf => cases v; cases w; rfl
  | advance T ih => cases v <;> cases w <;> simp only [finiteCascadeCommonPathDepth,ih]
  | fork T U ihT ihU =>
      cases v <;> cases w <;> simp only [finiteCascadeCommonPathDepth,ihT,ihU]

theorem nativeStreamingCommonClock_edge_same_time
    (q : ℕ → Paper.Overlap) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (e : NativeStreamingEdge T) (he : q (e.depth+1)=q e.depth)
    (v : FiniteCascadeRecordVertex T) :
    q (finiteCascadeCommonPathDepth T v (nativeStreamingEdgeParentVertex e)) =
      q (finiteCascadeCommonPathDepth T v (nativeStreamingEdgeChildVertex e)) := by
  induction e with
  | here T =>
      cases v with
      | root => rfl
      | child v =>
          simpa only [nativeStreamingEdgeParentVertex, nativeStreamingEdgeChildVertex,
            finiteCascadeCommonPathDepth,finiteCascadeCommonPathDepth_root_right] using he
  | child e ih =>
      cases v with
      | root => rfl
      | child v => exact ih he v
  | left e ih =>
      cases v with
      | root => rfl
      | left v => exact ih he v
      | right v => rfl
  | right e ih =>
      cases v with
      | root => rfl
      | left v => rfl
      | right v => exact ih he v

theorem nativeStreamingOriginCommonClock_vertex_edge_same_time
    (q : ℕ → Paper.Overlap) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (e : NativeStreamingEdge T) (he : q (e.depth+1)=q e.depth)
    (f : NativeStreamingEdge T) (r : Paper.Overlap)
    (hr : r ∈ Icc (q (f.depth+1)) (q f.depth)) :
    nativeStreamingOriginCommonClock q T
        (.vertex (nativeStreamingEdgeParentVertex e)) (.edge f r) =
      nativeStreamingOriginCommonClock q T
        (.vertex (nativeStreamingEdgeChildVertex e)) (.edge f r) := by
  induction e generalizing r with
  | @here j T =>
      cases f with
      | here =>
          have hrq : r=q j := le_antisymm hr.2 (he ▸ hr.1)
          subst r
          simp only [nativeStreamingOriginCommonClock,nativeStreamingEdgeParentVertex,
            nativeStreamingEdgeChildVertex,finiteCascadeCommonPathDepth,
            finiteCascadeCommonPathDepth_root_right,nativeStreamingOldSelectedCommonClock,
            NativeStreamingEdge.depth]
          simp only [Nat.succ_ne_self,ite_false,ite_true,he]
      | child f =>
          have hfj : j ≠ f.depth := (Nat.ne_of_lt f.depth_lt).symm
          have hfj1 : j+1 ≠ f.depth :=
            (Nat.ne_of_lt (f.depth_lt.trans (Nat.lt_succ_self j))).symm
          simp only [nativeStreamingOriginCommonClock,nativeStreamingEdgeParentVertex,
            nativeStreamingEdgeChildVertex,finiteCascadeCommonPathDepth,
            finiteCascadeCommonPathDepth_root_left,nativeStreamingOldSelectedCommonClock,
            NativeStreamingEdge.depth,if_neg hfj,if_neg hfj1]
          exact he
  | @child j T e ih =>
      cases f with
      | here =>
          simp only [nativeStreamingOriginCommonClock,nativeStreamingEdgeParentVertex,
            nativeStreamingEdgeChildVertex,finiteCascadeCommonPathDepth,
            finiteCascadeCommonPathDepth_root_right,nativeStreamingOldSelectedCommonClock,
            NativeStreamingEdge.depth,ite_true]
      | child f => exact ih he f r hr
  | left e ih =>
      cases f with
      | left f => exact ih he f r hr
      | right f => rfl
  | right e ih =>
      cases f with
      | left f => rfl
      | right f => exact ih he f r hr

end QuantitativeFollowup
