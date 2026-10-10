module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternCellDerivatives
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginComponentDerivative
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTermwiseSecondBracket

@[expose] public section

/-! Actual second streaming on the shared-future source term. The strict
future mask is fixed, both true cell measures are retained, and every
sum/interchange hypothesis follows from the actual joint integrability. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem sourceFuture_edge_fubini
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (Φ : NativeStreamingAttachmentPattern T→ℝ)
    (hi : ∀j∈Finset.range J,Integrable (fun z : Paper.Overlap×Paper.Overlap=>
      if z.1<z.2 then Φ (.future (.edge e z.1) j z.2) else 0)
      (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
        ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j))))) :
    (∫r in Ioc (q (e.depth+1)) (q e.depth),
      nativeStreamingPatternFutureFunctional μ a q T Φ (.edge e r) ∂parisiFreeMeasure μ a) =
      ∑j∈Finset.range J, ∫z : Paper.Overlap×Paper.Overlap,
        if z.1<z.2 then Φ (.future (.edge e z.1) j z.2) else 0
        ∂(((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
          ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))) := by
  simp only [nativeStreamingPatternFutureFunctional,nativeStreamingOriginLevel]
  rw [integral_finsetSum (Finset.range J) (fun j hj=>(hi j hj).integral_prod_left)]
  apply Finset.sum_congr rfl
  intro j hj
  exact (integral_prod _ (hi j hj)).symm

theorem hasDerivWithinAt_nativeStreamingPatternFuture_vertex_parameter_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (v : FiniteCascadeRecordVertex T) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>nativeStreamingPatternFutureFunctional μ a q T (fun P=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F P t) (.vertex v))
      (nativeStreamingPatternFutureFunctional μ a q T (fun P=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F P) (.vertex v)) (Icc (0:ℝ) 1) u := by
  simpa only [nativeStreamingPatternFutureFunctional,nativeStreamingOriginLevel,
    Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum (u := Finset.range J) (fun j _ =>
      hasDerivWithinAt_nativeStreamingPattern_future_vertex_integral_actual
        hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF v j u hu))

theorem hasDerivWithinAt_nativeStreamingPatternFuture_edge_parameter_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (e : NativeStreamingEdge T) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>∫r in Ioc (q (e.depth+1)) (q e.depth),
      nativeStreamingPatternFutureFunctional μ a q T (fun P=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F P t) (.edge e r) ∂parisiFreeMeasure μ a)
      (∫r in Ioc (q (e.depth+1)) (q e.depth),
        nativeStreamingPatternFutureFunctional μ a q T (fun P=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F P) (.edge e r) ∂parisiFreeMeasure μ a)
      (Icc (0:ℝ) 1) u := by
  have h : HasDerivWithinAt
      (fun t=>∑j∈Finset.range J, ∫z : Paper.Overlap×Paper.Overlap,
        if z.1<z.2 then nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F
          (.future (.edge e z.1) j z.2) t else 0
        ∂(((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
          ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))))
      (∑j∈Finset.range J, ∫z : Paper.Overlap×Paper.Overlap,
        if z.1<z.2 then (followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
          (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F
            (.future (.edge e z.1) j z.2) else 0
        ∂(((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
          ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))))
      (Icc (0:ℝ) 1) u := by
    simpa only [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum (u := Finset.range J) (fun j _ =>
        hasDerivWithinAt_nativeStreamingPattern_future_edge_integral_actual
          hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF e j u hu))
  have he := sourceFuture_edge_fubini μ a q T e (fun P=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F P)
    (fun j _=>(nativeStreamingPattern_future_edge_integral_regularities_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF e j u hu).2)
  rw [←he] at h
  apply h.congr_of_mem ?_ hu
  intro t ht
  exact sourceFuture_edge_fubini μ a q T e (fun P=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F P t)
    (fun j _=>(nativeStreamingPattern_future_edge_integral_regularities_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF e j t ht).1)

theorem hasDerivWithinAt_nativeStreamingSourceFuture_parameter_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>nativeStreamingOriginWeightIntegral μ a q T a
      (nativeStreamingPatternFutureFunctional μ a q T (fun P=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F P t)))
      (nativeStreamingOriginWeightIntegral μ a q T a
        (nativeStreamingPatternFutureFunctional μ a q T (fun P=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F P))) (Icc (0:ℝ) 1) u := by
  apply hasDerivWithinAt_nativeStreamingOriginWeightIntegral_of_components μ a q T a
  · intro v
    exact hasDerivWithinAt_nativeStreamingPatternFuture_vertex_parameter_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF v u hu
  · intro e
    exact hasDerivWithinAt_nativeStreamingPatternFuture_edge_parameter_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF e u hu

end QuantitativeFollowup
