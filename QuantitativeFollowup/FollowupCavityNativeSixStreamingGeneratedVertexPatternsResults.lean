module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexPatternsHistory
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexPatternsDefects

@[expose] public section

/-! Concrete interior atom receivers for the original/fresh and current
patterns. Every enlarged tree is genuinely constructed, and its complete
record law and terminal defect are transported inside the supporting cone.
These are atom receivers only; inherited-CDF and edge receivers are separate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem nativeStreamingGeneratedVertexAtom_originalFresh_receiver
    (ν : Measure Paper.Overlap) [IsFiniteMeasure ν]
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < W.depth)
    (F : TerminalSpins (Configuration (n+1)) W.tree → ℝ) (i : ObservationLeaf W.tree) :
    (∫ H, nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ .single) H)
      W.tree v .single
      (nativeStreamingOriginalFreshSpinTest W.tree F i
        (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ .single) H
          (finiteCascadeCommonPathDepth W.tree (observationLeafVertex W.tree i) v)))
      ∂(nativeStreamingGeneratedVertexAtomProgram
        (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) W v).measure ν) =
    ∫ h, ν.real {nativeStreamingGeneratedComponentClock W h v.depth} *
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree F (.originalFresh i (.vertex v))
      ∂(P.measure ν).restrict (nativeStreamingGeneratedComponentOrderSet W) := by
  have h := nativeStreamingGeneratedVertexMoment_ordered_atom_receiver_real ν P D μ a W v hv0 hvJ .single
    (fun q => nativeStreamingOriginalFreshSpinTest W.tree F i
      (q (finiteCascadeCommonPathDepth W.tree (observationLeafVertex W.tree i) v)))
    (fun σ => continuous_nativeStreamingOriginalFreshSpinTest_clock W.tree F i _
      (nativeStreamingGeneratedComponentClock_continuous W _) σ)
  apply h.trans
  apply integral_congr_ae
  exact .of_forall fun h => congrArg
    (fun x => ν.real {nativeStreamingGeneratedComponentClock W h v.depth} * x)
    (nativeStreamingGeneratedVertexMoment_originalFresh D μ a _ W.tree v F i)

theorem nativeStreamingGeneratedVertexAtom_current_receiver
    (ν : Measure Paper.Overlap) [IsFiniteMeasure ν]
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < W.depth)
    (F : TerminalSpins (Configuration (n+1)) W.tree → ℝ) :
    (∫ H, nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ .current) H)
      W.tree v .current
      (nativeStreamingDefectSpinTest W.tree F
        (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ .current) H v.depth))
      ∂(nativeStreamingGeneratedVertexAtomProgram
        (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) W v).measure ν) =
    ∫ h, ν.real {nativeStreamingGeneratedComponentClock W h v.depth} *
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree F (.current (.vertex v))
      ∂(P.measure ν).restrict (nativeStreamingGeneratedComponentOrderSet W) := by
  have h := nativeStreamingGeneratedVertexMoment_ordered_atom_receiver_real ν P D μ a W v hv0 hvJ .current
    (fun q => nativeStreamingDefectSpinTest W.tree F (q v.depth))
    (fun σ => continuous_nativeStreamingDefectSpinTest_clock W.tree F _
      (nativeStreamingGeneratedComponentClock_continuous W v.depth) σ)
  apply h.trans
  apply integral_congr_ae
  exact .of_forall fun h => congrArg
    (fun x => ν.real {nativeStreamingGeneratedComponentClock W h v.depth} * x)
    (nativeStreamingGeneratedVertexMoment_current D μ a _ W.tree v F)

theorem integrable_nativeStreamingGeneratedVertexAtom_originalFresh_receiver
    (ν : Measure Paper.Overlap) [SFinite ν] (hν : ν univ ≤ 1)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < W.depth)
    (F : TerminalSpins (Configuration (n+1)) W.tree → ℝ) (i : ObservationLeaf W.tree)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀σ, |F σ| ≤ C) :
    Integrable (fun H => nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ .single) H)
      W.tree v .single
      (nativeStreamingOriginalFreshSpinTest W.tree F i
        (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ .single) H
          (finiteCascadeCommonPathDepth W.tree (observationLeafVertex W.tree i) v))))
      ((nativeStreamingGeneratedVertexAtomProgram
        (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) W v).measure ν) := by
  exact integrable_nativeStreamingGeneratedVertexMoment_ordered_atom_receiver ν hν P D μ a W v hv0 hvJ .single
    (fun q => nativeStreamingOriginalFreshSpinTest W.tree F i
      (q (finiteCascadeCommonPathDepth W.tree (observationLeafVertex W.tree i) v)))
    (fun σ => continuous_nativeStreamingOriginalFreshSpinTest_clock W.tree F i _
      (nativeStreamingGeneratedComponentClock_continuous W _) σ)
    (2*C) (fun q σ => nativeStreamingOriginalFreshSpinTest_abs_le W.tree F C hC hF i _ σ)

theorem integrable_nativeStreamingGeneratedVertexAtom_current_receiver
    (ν : Measure Paper.Overlap) [SFinite ν] (hν : ν univ ≤ 1)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < W.depth)
    (F : TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀σ, |F σ| ≤ C) :
    Integrable (fun H => nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ .current) H)
      W.tree v .current
      (nativeStreamingDefectSpinTest W.tree F
        (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ .current) H v.depth)))
      ((nativeStreamingGeneratedVertexAtomProgram
        (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) W v).measure ν) := by
  exact integrable_nativeStreamingGeneratedVertexMoment_ordered_atom_receiver ν hν P D μ a W v hv0 hvJ .current
    (fun q => nativeStreamingDefectSpinTest W.tree F (q v.depth))
    (fun σ => continuous_nativeStreamingDefectSpinTest_clock W.tree F _
      (nativeStreamingGeneratedComponentClock_continuous W v.depth) σ)
    (2*C) (fun q σ => nativeStreamingDefectSpinTest_abs_le W.tree F C hC hF _ σ)

end QuantitativeFollowup
