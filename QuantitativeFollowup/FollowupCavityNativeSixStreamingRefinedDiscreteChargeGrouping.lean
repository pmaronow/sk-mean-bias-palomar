module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedDiscreteChargeBlocks

@[expose] public section

/-! Exact normalized finite-profile charge regrouping onto the original
genealogy. The callback inputs are structural old-vertex, selected-slot
and child-endpoint identities; no integral or charge conclusion is an
input. Both the first upper cell and the final root correction survive. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {k J : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem refinedDiscrete_root_coherent_pad {j : ℕ}
    (T : FiniteTerminalGenealogy j) (t : ℕ)
    (Φ : FiniteCascadeRecordVertex (observationTreePad T t) → ℝ)
    (hΦ : nativeStreamingRootCoherent (observationTreePad T t) Φ) :
    nativeStreamingRootCoherent T (fun v => Φ (nativeStreamingPadVertexEmbed T t v)) := by
  induction t with
  | zero => exact hΦ
  | succ t ih => exact ih (fun v => Φ (.child v)) hΦ

theorem nativeStreamingNormalizedRefinedChargeSum_eq_originWeightIntegral
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (hfloor : Paper.parisiSchemeMeasure (cdfMassScheme s) ∈ scalarFloor a)
    (q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hlevels : ∀i, anisotropicRecordedSchemeSchedule (cdfMassScheme s)
      (observationRefinementDepth d i) = q i)
    (T : FiniteTerminalGenealogy J) (hdepth : observationRefinementDepth d J ≤ k+1)
    (incoming : ℝ)
    (Φ : FiniteCascadeRecordVertex (observationRefineTree d T) → ℝ)
    (Ψ : NativeStreamingOrigin T → ℝ)
    (hΦ : nativeStreamingRootCoherent (observationRefineTree d T) Φ)
    (hvertex : ∀v, Φ (nativeStreamingRefinementVertexEmbed d T v) = Ψ (.vertex v))
    (hselected : ∀(e : NativeStreamingEdge T) p, p < d e.depth →
      Φ (nativeStreamingEdgeSelectedVertex d e p) =
        Ψ (.edge e (anisotropicRecordedSchemeSchedule (cdfMassScheme s)
          (observationRefinementDepth d e.depth+p+1))))
    (hendpoint : ∀e : NativeStreamingEdge T,
      Ψ (.edge e (q e.depth)) = Ψ (.vertex (nativeStreamingEdgeChildVertex e))) :
    nativeStreamingVertexChargeSum (anisotropicSchemeMass (cdfMassScheme s)) incoming
      (observationRefineTree d T) Φ =
      nativeStreamingOriginWeightIntegral (Paper.parisiSchemeMeasure (cdfMassScheme s))
        a q T incoming Ψ := by
  let μ := Paper.parisiSchemeMeasure (cdfMassScheme s)
  let Q := anisotropicRecordedSchemeSchedule (cdfMassScheme s)
  let b := anisotropicSchemeMass (cdfMassScheme s)
  change nativeStreamingVertexChargeSum b incoming (observationRefineTree d T) Φ =
    nativeStreamingOriginWeightIntegral μ a q T incoming Ψ
  revert hdepth incoming Φ Ψ
  induction T with
  | leaf =>
      intro hdepth incoming Φ Ψ hΦ hvertex hselected hendpoint
      simp only [nativeStreamingVertexChargeSum, finiteCascadeVertexCharges,
        finiteCascadeVertexInteriorCharges, finiteCascadeTreeRootCoefficient,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        nativeStreamingOriginWeightIntegral]
      rw [hvertex (.root .leaf)]
  | @advance j T ih =>
      intro hdepth incoming Φ Ψ hΦ hvertex hselected hendpoint
      have hbound : observationRefinementDepth d j+d j+1 ≤ k+1 := hdepth
      have hchildDepth : observationRefinementDepth d j ≤ k+1 := by omega
      have hchildCoherent : nativeStreamingRootCoherent (observationRefineTree d T)
          (fun v => Φ (.child (nativeStreamingPadVertexEmbed (observationRefineTree d T) (d j) v))) :=
        refinedDiscrete_root_coherent_pad (observationRefineTree d T) (d j) (fun v => Φ (.child v)) hΦ
      have hvchild : ∀v,
          Φ (.child (nativeStreamingPadVertexEmbed (observationRefineTree d T) (d j)
            (nativeStreamingRefinementVertexEmbed d T v))) =
          Ψ (nativeStreamingOriginChild (.vertex v)) := fun v => hvertex (.child v)
      have hschild : ∀(e : NativeStreamingEdge T) p, p < d e.depth →
          Φ (.child (nativeStreamingPadVertexEmbed (observationRefineTree d T) (d j)
            (nativeStreamingEdgeSelectedVertex d e p))) =
          Ψ (nativeStreamingOriginChild (.edge e (Q (observationRefinementDepth d e.depth+p+1)))) :=
        fun e p hp => hselected (.child e) p hp
      have hechild : ∀e : NativeStreamingEdge T,
          Ψ (nativeStreamingOriginChild (.edge e (q e.depth))) =
          Ψ (nativeStreamingOriginChild (.vertex (nativeStreamingEdgeChildVertex e))) :=
        fun e => hendpoint (.child e)
      have Hchild := ih hchildDepth (Paper.parisiCDF μ (q j))
        (fun v => Φ (.child (nativeStreamingPadVertexEmbed (observationRefineTree d T) (d j) v)))
        (fun o => Ψ (nativeStreamingOriginChild o)) hchildCoherent hvchild hschild hechild
      have Hcell := nativeStreamingNormalizedScheme_Ioc_pad_cells s a ha hfloor
        (observationRefinementDepth d j) (d j) hbound
        (fun r => Ψ (.edge (.here T) r))
      dsimp only at Hcell
      rw [show observationRefinementDepth d j+d j+1 = observationRefinementDepth d (j+1) from rfl,
        hlevels (j+1), hlevels j] at Hcell
      rw [hendpoint (.here T)] at Hcell
      have hlast : b (observationRefinementDepth d j+d j) = Paper.parisiCDF μ (q (j+1)) := by
        change anisotropicSchemeMass (cdfMassScheme s)
          (observationRefinementDepth d j+d j) = Paper.parisiCDF μ (q (j+1))
        rw [nativeStreamingNormalizedSchemeMass_eq_lower_CDF s
          (observationRefinementDepth d j+d j) (by omega)]
        change Paper.parisiCDF μ (anisotropicRecordedSchemeSchedule (cdfMassScheme s)
          (observationRefinementDepth d j+d j+1)) = _
        rw [show observationRefinementDepth d j+d j+1 = observationRefinementDepth d (j+1) from rfl,
          hlevels (j+1)]
      have Hsum :
          (∑p ∈ Finset.range (d j),
            (b (observationRefinementDepth d j+p)-b (observationRefinementDepth d j+p+1)) *
              Φ (nativeStreamingEdgeSelectedVertex d (.here T) p)) =
          ∑p ∈ Finset.range (d j),
            (b (observationRefinementDepth d j+p)-b (observationRefinementDepth d j+p+1)) *
              Ψ (.edge (.here T) (Q (observationRefinementDepth d j+p+1))) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hselected (.here T) p (Finset.mem_range.mp hp)]
      rw [nativeStreamingVertexChargeSum_pad_block,
        nativeStreamingVertexChargeSum_change_incoming b (observationRefineTree d T)
          (b (observationRefinementDepth d j)) (Paper.parisiCDF μ (q j)), Hchild]
      rw [Hsum, hlast]
      have hroot := hvertex (.root T.advance)
      have hchildRoot := hvertex (.child (.root T))
      rw [nativeStreamingRefinementVertexEmbed_root] at hroot
      change Φ (.child (nativeStreamingPadVertexEmbed (observationRefineTree d T) (d j)
        (nativeStreamingRefinementVertexEmbed d T (.root T)))) =
          Ψ (.vertex (.child (.root T))) at hchildRoot
      rw [nativeStreamingRefinementVertexEmbed_root] at hchildRoot
      rw [hroot, hchildRoot]
      change _ = nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o => Ψ (nativeStreamingOriginChild o)) +
        (∫r in Ioc (q (j+1)) (q j), Ψ (.edge (.here T) r) ∂parisiFreeMeasure μ a) +
        (Paper.parisiCDF μ (q (j+1))-incoming)*Ψ (.vertex (.root T.advance))
      rw [Hcell]
      simp only [μ, b, Q, nativeStreamingEdgeChildVertex, add_assoc]
  | @fork j T U ihT ihU =>
      intro hdepth incoming Φ Ψ hΦ hvertex hselected hendpoint
      obtain ⟨hleft, hright, hT, hU⟩ := hΦ
      have hvT : ∀v, Φ (.left (nativeStreamingRefinementVertexEmbed d T v)) =
          Ψ (nativeStreamingOriginLeft (.vertex v)) := fun v => hvertex (.left v)
      have hvU : ∀v, Φ (.right (nativeStreamingRefinementVertexEmbed d U v)) =
          Ψ (nativeStreamingOriginRight (.vertex v)) := fun v => hvertex (.right v)
      have hsT : ∀(e : NativeStreamingEdge T) p, p < d e.depth →
          Φ (.left (nativeStreamingEdgeSelectedVertex d e p)) =
          Ψ (nativeStreamingOriginLeft (.edge e (Q (observationRefinementDepth d e.depth+p+1)))) :=
        fun e p hp => hselected (.left e) p hp
      have hsU : ∀(e : NativeStreamingEdge U) p, p < d e.depth →
          Φ (.right (nativeStreamingEdgeSelectedVertex d e p)) =
          Ψ (nativeStreamingOriginRight (.edge e (Q (observationRefinementDepth d e.depth+p+1)))) :=
        fun e p hp => hselected (.right e) p hp
      have heT : ∀e : NativeStreamingEdge T,
          Ψ (nativeStreamingOriginLeft (.edge e (q e.depth))) =
          Ψ (nativeStreamingOriginLeft (.vertex (nativeStreamingEdgeChildVertex e))) :=
        fun e => hendpoint (.left e)
      have heU : ∀e : NativeStreamingEdge U,
          Ψ (nativeStreamingOriginRight (.edge e (q e.depth))) =
          Ψ (nativeStreamingOriginRight (.vertex (nativeStreamingEdgeChildVertex e))) :=
        fun e => hendpoint (.right e)
      have HT := ihT hdepth (Paper.parisiCDF μ (q j)) (fun v => Φ (.left v))
        (fun o => Ψ (nativeStreamingOriginLeft o)) hT hvT hsT heT
      have HU := ihU hdepth (Paper.parisiCDF μ (q j)) (fun v => Φ (.right v))
        (fun o => Ψ (nativeStreamingOriginRight o)) hU hvU hsU heU
      rw [nativeStreamingVertexChargeSum_fork b _ _ incoming _ hleft hright,
        nativeStreamingVertexChargeSum_change_incoming b (observationRefineTree d T) (b (observationRefinementDepth d j))
          (Paper.parisiCDF μ (q j)),
        nativeStreamingVertexChargeSum_change_incoming b (observationRefineTree d U) (b (observationRefinementDepth d j))
          (Paper.parisiCDF μ (q j)), HT, HU, hleft, hright]
      have hroot := hvertex (.root (T.fork U))
      rw [nativeStreamingRefinementVertexEmbed_root] at hroot
      rw [hroot]
      change _ = nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o => Ψ (nativeStreamingOriginLeft o)) +
        nativeStreamingOriginWeightIntegral μ a q U (Paper.parisiCDF μ (q j))
          (fun o => Ψ (nativeStreamingOriginRight o)) +
        (2*Paper.parisiCDF μ (q j)-incoming)*Ψ (.vertex (.root (T.fork U)))
      ring

end QuantitativeFollowup
