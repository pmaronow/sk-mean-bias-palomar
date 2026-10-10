module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedMixedCrossPatternsMoments

@[expose] public section

/-! Explicit terminal and whole-record bridges for the constructed mixed
receiver. Both fresh spins and every original record are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

def nativeStreamingGeneratedMixedCrossTerminalTest
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (F : CavityGeneratedHistory Paper.Overlap m→TerminalSpins (Configuration (n+1)) W.tree→ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    TerminalSpins (Configuration (n+1)) (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ).tree→ℝ :=
  let U := nativeStreamingGeneratedEdgeObservedComponent W e
  let t := nativeStreamingGeneratedEdgeVertex W e
  let w := nativeStreamingGeneratedMixedRefinedVertex W e v
  let q := nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ) H
  nativeStreamingPatternRefinedCrossTerminalTest (nativeStreamingEdgeSubdivision e.depth) W.tree t w
    (nativeStreamingDefectSpinTest W.tree (F (nativeStreamingGeneratedCrossVertexPrefix H))
      (q (finiteCascadeCommonPathDepth U.tree t w)))

theorem nativeStreamingGeneratedMixedCrossPatternMoment_eq_oldTerminalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (F : CavityGeneratedHistory Paper.Overlap m→TerminalSpins (Configuration (n+1)) W.tree→ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    nativeStreamingGeneratedMixedCrossPatternMoment D μ a W e v hv0 hvJ F H=
      nativeStreamingOldTerminalExpectation D μ a
        (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ) H)
        (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ).tree
        (nativeStreamingGeneratedMixedCrossTerminalTest W e v hv0 hvJ F H) := rfl

theorem nativeStreamingGeneratedMixedCrossTerminalTest_abs_le
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (F : CavityGeneratedHistory Paper.Overlap m→TerminalSpins (Configuration (n+1)) W.tree→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀h σ,|F h σ|≤C)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : TerminalSpins (Configuration (n+1)) (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ).tree) :
    |nativeStreamingGeneratedMixedCrossTerminalTest W e v hv0 hvJ F H σ|≤2*C := by
  apply nativeStreamingDefectSpinTest_abs_le W.tree _ C hC (hF _)

def nativeStreamingGeneratedMixedCrossRecordProjection {E S : Type}
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (z : E × Records E S (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ).tree) :
    (E × Records E S W.tree) × (S×S) :=
  let c := finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin
    (nativeStreamingGeneratedEdgeVertex W e) (nativeStreamingGeneratedMixedRefinedVertex W e v) z.2
  ((z.1,observationRefinementProject (nativeStreamingEdgeSubdivision e.depth) W.tree c.1),c.2)

theorem measurable_nativeStreamingGeneratedMixedCrossRecordProjection {n : ℕ}
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth) :
    Measurable (nativeStreamingGeneratedMixedCrossRecordProjection
      (E:=AnisotropicObservationState n) (S:=Configuration n) W e v hv0 hvJ) := by
  have he := measurable_finiteCascadeCrossContinuationExtract (E:=AnisotropicObservationState n)
    (S:=Configuration n) observationLinearTree observationLinearSpin
    (fun j=>measurable_observationLinearSpin j)
    (nativeStreamingGeneratedEdgeVertex W e) (nativeStreamingGeneratedMixedRefinedVertex W e v)
  exact (measurable_fst.prodMk ((measurable_observationRefinementProject
    (nativeStreamingEdgeSubdivision e.depth) W.tree).comp (he.fst.comp measurable_snd))).prodMk
      (he.snd.comp measurable_snd)

theorem nativeStreamingGeneratedMixedCross_enlarged_record_projection
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (v : FiniteCascadeRecordVertex W.tree) (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (b : Fin m) (hb : cavityGeneratedFiniteClockLabels W.label v.depth=.mark b)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧
      r≤nativeStreamingGeneratedComponentClock W h e.depth) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ)
        (nativeStreamingGeneratedMixedCrossAppend b h r))
      (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ).tree).map
        (nativeStreamingGeneratedMixedCrossRecordProjection W e v hv0 hvJ)=
      (nativeStreamingOriginCrossProbability D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (.edge e r) (.vertex v) : Measure _) := by
  let U := nativeStreamingGeneratedEdgeObservedComponent W e
  let t := nativeStreamingGeneratedEdgeVertex W e
  let w := nativeStreamingGeneratedMixedRefinedVertex W e v
  let ψ := fun z : AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n)
        (finiteCascadeCrossContinuationGraft observationLinearTree t w)=>
      ((z.1,(finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin t w z.2).1),
        (finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin t w z.2).2)
  let π := fun z : (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) U.tree) × (Configuration n×Configuration n)=>
      ((z.1.1,observationRefinementProject (nativeStreamingEdgeSubdivision e.depth) W.tree z.1.2),z.2)
  have he := measurable_finiteCascadeCrossContinuationExtract (E:=AnisotropicObservationState n)
    (S:=Configuration n) observationLinearTree observationLinearSpin
    (fun j=>measurable_observationLinearSpin j) t w
  have hψ : Measurable ψ :=
    (measurable_fst.prodMk (he.fst.comp measurable_snd)).prodMk (he.snd.comp measurable_snd)
  have hπ : Measurable π :=
    (measurable_fst.fst.prodMk ((measurable_observationRefinementProject
      (nativeStreamingEdgeSubdivision e.depth) W.tree).comp measurable_fst.snd)).prodMk measurable_snd
  let X := (AnisotropicObservationState n ×
    Records (AnisotropicObservationState n) (Configuration n) W.tree) × (Configuration n×Configuration n)
  have H := congrArg (fun P : ProbabilityMeasure X=>(P : Measure X))
    (nativeStreamingGeneratedMixedCross_full_record_law D μ a W e v hv0 hvJ b hb h r hh hr)
  change ((anisotropicRecordedProfileTreeLaw D μ a
    (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedMixedCrossComponent W e v hv0 hvJ)
      (nativeStreamingGeneratedMixedCrossAppend b h r)) _).map ψ).map π=_ at H
  rw [Measure.map_map hπ hψ] at H
  exact H

end QuantitativeFollowup
