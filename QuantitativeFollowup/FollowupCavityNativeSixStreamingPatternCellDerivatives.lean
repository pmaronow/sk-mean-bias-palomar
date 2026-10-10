module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternIntegralDerivative
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternMarkMeasurable

@[expose] public section

/-! Actual termwise source differentiation on genuine fixed mark cells.
All selector validity, slice measurability and dominated-integral inputs
are discharged by the actual model and the normalized marked laws. The
future cells keep their literal strict mask; product cells keep both
original attachment variables. -/
noncomputable section
open Set Filter MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem hasDerivWithinAt_nativeStreamingPattern_originalFresh_edge_integral_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (i : ObservationLeaf T) (e : NativeStreamingEdge T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>∫r,nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.originalFresh i (.edge e r)) t ∂((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))))
      (∫r,(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.originalFresh i (.edge e r)) ∂((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth)))) (Icc (0:ℝ) 1) u := by
  apply hasDerivWithinAt_nativeStreamingPattern_selected_integral
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) (fun r=>.originalFresh i (.edge e r))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ⟨hr.1.le,hr.2⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_originalFresh_edge_Ioc
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F i e

theorem hasDerivWithinAt_nativeStreamingPattern_current_edge_integral_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (e : NativeStreamingEdge T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>∫r,nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.current (.edge e r)) t ∂((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))))
      (∫r,(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.current (.edge e r)) ∂((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth)))) (Icc (0:ℝ) 1) u := by
  apply hasDerivWithinAt_nativeStreamingPattern_selected_integral
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) (fun r=>.current (.edge e r))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ⟨hr.1.le,hr.2⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_current_edge_Ioc
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F e

theorem hasDerivWithinAt_nativeStreamingPattern_cross_edge_vertex_integral_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (e : NativeStreamingEdge T) (w : FiniteCascadeRecordVertex T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>∫r,nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.cross (.edge e r) (.vertex w)) t ∂((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))))
      (∫r,(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.cross (.edge e r) (.vertex w)) ∂((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth)))) (Icc (0:ℝ) 1) u := by
  apply hasDerivWithinAt_nativeStreamingPattern_selected_integral
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) (fun r=>.cross (.edge e r) (.vertex w))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ⟨⟨hr.1.le,hr.2⟩,trivial⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_cross_edge_vertex_Ioc
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F e w

theorem hasDerivWithinAt_nativeStreamingPattern_cross_vertex_edge_integral_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (v : FiniteCascadeRecordVertex T) (e : NativeStreamingEdge T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>∫r,nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.cross (.vertex v) (.edge e r)) t ∂((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))))
      (∫r,(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.cross (.vertex v) (.edge e r)) ∂((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth)))) (Icc (0:ℝ) 1) u := by
  apply hasDerivWithinAt_nativeStreamingPattern_selected_integral
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) (fun r=>.cross (.vertex v) (.edge e r))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ⟨trivial,⟨hr.1.le,hr.2⟩⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_cross_vertex_edge_Ioc
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F v e

theorem hasDerivWithinAt_nativeStreamingPattern_cross_edges_integral_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (e f : NativeStreamingEdge T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>∫(z : Paper.Overlap×Paper.Overlap),nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.cross (.edge e z.1) (.edge f z.2)) t ∂(((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod ((parisiFreeMeasure μ a).restrict (Ioc (q (f.depth+1)) (q f.depth)))))
      (∫(z : Paper.Overlap×Paper.Overlap),(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.cross (.edge e z.1) (.edge f z.2)) ∂(((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod ((parisiFreeMeasure μ a).restrict (Ioc (q (f.depth+1)) (q f.depth))))) (Icc (0:ℝ) 1) u := by
  apply hasDerivWithinAt_nativeStreamingPattern_selected_integral
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod ((parisiFreeMeasure μ a).restrict (Ioc (q (f.depth+1)) (q f.depth)))) (fun z=>.cross (.edge e z.1) (.edge f z.2))
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hr
    exact ⟨⟨hr.1.1.le,hr.1.2⟩,⟨hr.2.1.le,hr.2.2⟩⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_cross_edges_Ioc_prod
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F e f

theorem hasDerivWithinAt_nativeStreamingPattern_future_vertex_integral_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (v : FiniteCascadeRecordVertex T) (j : ℕ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>∫l,if q v.depth<l then nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.future (.vertex v) j l) t else 0 ∂((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j))))
      (∫l,if q v.depth<l then (followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.future (.vertex v) j l) else 0 ∂((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))) (Icc (0:ℝ) 1) u := by
  apply hasDerivWithinAt_nativeStreamingPattern_masked_integral
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j))) (fun l=>.future (.vertex v) j l) (fun l=>q v.depth<l)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hr
    exact ⟨trivial,⟨hr.1.le,hr.2⟩⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_future_vertex_Ioc
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F v j

theorem hasDerivWithinAt_nativeStreamingPattern_future_edge_integral_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (e : NativeStreamingEdge T) (j : ℕ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>∫(z : Paper.Overlap×Paper.Overlap),if z.1<z.2 then nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.future (.edge e z.1) j z.2) t else 0 ∂(((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))))
      (∫(z : Paper.Overlap×Paper.Overlap),if z.1<z.2 then (followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.future (.edge e z.1) j z.2) else 0 ∂(((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j))))) (Icc (0:ℝ) 1) u := by
  apply hasDerivWithinAt_nativeStreamingPattern_masked_integral
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))) (fun z=>.future (.edge e z.1) j z.2) (fun z=>z.1<z.2)
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hr
    exact ⟨⟨hr.1.1.le,hr.1.2⟩,⟨hr.2.1.le,hr.2.2⟩⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_future_edge_Ioc_prod
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F e j

theorem hasDerivWithinAt_nativeStreamingPattern_normalizer_integral_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>∫l,nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.normalizer l) t ∂(parisiFreeMeasure μ a))
      (∫l,(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.normalizer l) ∂(parisiFreeMeasure μ a)) (Icc (0:ℝ) 1) u := by
  apply hasDerivWithinAt_nativeStreamingPattern_selected_integral
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    (parisiFreeMeasure μ a) (fun l=>.normalizer l)
  · exact .of_forall fun _=>trivial
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_normalizer
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q T F 

theorem nativeStreamingPattern_originalFresh_edge_integral_regularities_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (i : ObservationLeaf T) (e : NativeStreamingEdge T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Integrable (fun r=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.originalFresh i (.edge e r)) u) ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) ∧
    Integrable (fun r=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.originalFresh i (.edge e r))) ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) := by
  apply nativeStreamingPattern_selected_integral_regularities
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) (fun r=>.originalFresh i (.edge e r))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ⟨hr.1.le,hr.2⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_originalFresh_edge_Ioc
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F i e

theorem nativeStreamingPattern_current_edge_integral_regularities_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (e : NativeStreamingEdge T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Integrable (fun r=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.current (.edge e r)) u) ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) ∧
    Integrable (fun r=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.current (.edge e r))) ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) := by
  apply nativeStreamingPattern_selected_integral_regularities
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) (fun r=>.current (.edge e r))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ⟨hr.1.le,hr.2⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_current_edge_Ioc
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F e

theorem nativeStreamingPattern_cross_edge_vertex_integral_regularities_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (e : NativeStreamingEdge T) (w : FiniteCascadeRecordVertex T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Integrable (fun r=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.cross (.edge e r) (.vertex w)) u) ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) ∧
    Integrable (fun r=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.cross (.edge e r) (.vertex w))) ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) := by
  apply nativeStreamingPattern_selected_integral_regularities
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) (fun r=>.cross (.edge e r) (.vertex w))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ⟨⟨hr.1.le,hr.2⟩,trivial⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_cross_edge_vertex_Ioc
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F e w

theorem nativeStreamingPattern_cross_vertex_edge_integral_regularities_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (v : FiniteCascadeRecordVertex T) (e : NativeStreamingEdge T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Integrable (fun r=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.cross (.vertex v) (.edge e r)) u) ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) ∧
    Integrable (fun r=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.cross (.vertex v) (.edge e r))) ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) := by
  apply nativeStreamingPattern_selected_integral_regularities
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) (fun r=>.cross (.vertex v) (.edge e r))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ⟨trivial,⟨hr.1.le,hr.2⟩⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_cross_vertex_edge_Ioc
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F v e

theorem nativeStreamingPattern_cross_edges_integral_regularities_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (e f : NativeStreamingEdge T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Integrable (fun z : Paper.Overlap×Paper.Overlap=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.cross (.edge e z.1) (.edge f z.2)) u) (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod ((parisiFreeMeasure μ a).restrict (Ioc (q (f.depth+1)) (q f.depth)))) ∧
    Integrable (fun z : Paper.Overlap×Paper.Overlap=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.cross (.edge e z.1) (.edge f z.2))) (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod ((parisiFreeMeasure μ a).restrict (Ioc (q (f.depth+1)) (q f.depth)))) := by
  apply nativeStreamingPattern_selected_integral_regularities
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod ((parisiFreeMeasure μ a).restrict (Ioc (q (f.depth+1)) (q f.depth)))) (fun z=>.cross (.edge e z.1) (.edge f z.2))
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hr
    exact ⟨⟨hr.1.1.le,hr.1.2⟩,⟨hr.2.1.le,hr.2.2⟩⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_cross_edges_Ioc_prod
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F e f

theorem nativeStreamingPattern_future_vertex_integral_regularities_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (v : FiniteCascadeRecordVertex T) (j : ℕ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Integrable (fun l=>if q v.depth<l then nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.future (.vertex v) j l) u else 0) ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j))) ∧
    Integrable (fun l=>if q v.depth<l then (followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.future (.vertex v) j l) else 0) ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j))) := by
  apply nativeStreamingPattern_masked_integral_regularities
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j))) (fun l=>.future (.vertex v) j l) (fun l=>q v.depth<l)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hr
    exact ⟨trivial,⟨hr.1.le,hr.2⟩⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_future_vertex_Ioc
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F v j

theorem nativeStreamingPattern_future_edge_integral_regularities_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (e : NativeStreamingEdge T) (j : ℕ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Integrable (fun z : Paper.Overlap×Paper.Overlap=>if z.1<z.2 then nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.future (.edge e z.1) j z.2) u else 0) (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))) ∧
    Integrable (fun z : Paper.Overlap×Paper.Overlap=>if z.1<z.2 then (followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.future (.edge e z.1) j z.2) else 0) (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))) := by
  apply nativeStreamingPattern_masked_integral_regularities
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))) (fun z=>.future (.edge e z.1) j z.2) (fun z=>z.1<z.2)
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hr
    exact ⟨⟨hr.1.1.le,hr.1.2⟩,⟨hr.2.1.le,hr.2.2⟩⟩
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_future_edge_Ioc_prod
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F e j

theorem nativeStreamingPattern_normalizer_integral_regularities_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Integrable (fun l=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.normalizer l) u) (parisiFreeMeasure μ a) ∧
    Integrable (fun l=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.normalizer l)) (parisiFreeMeasure μ a) := by
  apply nativeStreamingPattern_selected_integral_regularities
    hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF
    (parisiFreeMeasure μ a) (fun l=>.normalizer l)
  · exact .of_forall fun _=>trivial
  · intro t ht
    exact aestronglyMeasurable_nativeStreamingPatternMoment_normalizer
      (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q T F 

end QuantitativeFollowup
