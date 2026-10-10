module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossVertexPatternsConstruction
public import FourPapersCommon.FiniteJointLaw

@[expose] public section

/-! The two genuine atom instructions have exactly the product of the
original vertex singleton masses. The full old prefix is retained; no
clock is taken from an intermediate grafted component. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

theorem nativeStreamingGeneratedCrossVertexAtomProgram_measure
    (ν : Measure Paper.Overlap) [SFinite ν]
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree) :
    (nativeStreamingGeneratedCrossVertexAtomProgram P W v w).measure ν=
      ((P.measure ν).withDensity (fun h =>
        ν {(cavityGeneratedFiniteClockLabels W.label v.depth).value h} *
        ν {(cavityGeneratedFiniteClockLabels W.label w.depth).value h})).map
          (nativeStreamingGeneratedCrossVertexAppend W v w) := by
  let qv := (cavityGeneratedFiniteClockLabels W.label v.depth).value
  let qw := (cavityGeneratedFiniteClockLabels W.label w.depth).value
  let A : CavityGeneratedHistory Paper.Overlap m → CavityGeneratedHistory Paper.Overlap (m+1) :=
    fun h => Fin.snoc h (qv h)
  let B : CavityGeneratedHistory Paper.Overlap (m+1) → CavityGeneratedHistory Paper.Overlap (m+2) := fun H =>
    Fin.snoc H (qw (cavityGeneratedHistoryPrefix H))
  let fv := fun h : CavityGeneratedHistory Paper.Overlap m => ν {qv h}
  let fw := fun h : CavityGeneratedHistory Paper.Overlap m => ν {qw h}
  let G := fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
    ν {qw (cavityGeneratedHistoryPrefix H)}
  have hqv : Measurable qv := (cavityGeneratedFiniteClockLabels W.label v.depth).continuous_value.measurable
  have hqw : Measurable qw := (cavityGeneratedFiniteClockLabels W.label w.depth).continuous_value.measurable
  have hA : Measurable A := cavityGeneratedHistorySnoc_measurable qv hqv
  have hB : Measurable B := cavityGeneratedHistorySnoc_measurable _
    (hqw.comp cavityGeneratedHistoryPrefix_measurable)
  have hfv : Measurable fv := measurable_nativeStreamingGeneratedAtomMass ν qv hqv
  have hfw : Measurable fw := measurable_nativeStreamingGeneratedAtomMass ν qw hqw
  have hG : Measurable G := hfw.comp cavityGeneratedHistoryPrefix_measurable
  have heG : (fun h => G (A h))=fw := by
    funext h
    simp only [G,A,cavityGeneratedHistoryPrefix_snoc,fw]
  change ((((P.measure ν).withDensity fv).map A).withDensity G).map B = _
  rw [←map_withDensity_pullback _ A hA G hG,heG,
    Measure.map_map hB hA,←withDensity_mul (P.measure ν) hfv hfw]
  congr 1
  funext h
  simp only [Function.comp_def,B,A,nativeStreamingGeneratedCrossVertexAppend,
    cavityGeneratedHistoryPrefix_snoc,qv,qw]

theorem nativeStreamingGeneratedCrossVertexAtomProgram_prefix_law
    (ν : Measure Paper.Overlap) [SFinite ν]
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree) :
    ((nativeStreamingGeneratedCrossVertexAtomProgram P W v w).measure ν).map
      nativeStreamingGeneratedCrossVertexPrefix=
      (P.measure ν).withDensity (fun h =>
        ν {(cavityGeneratedFiniteClockLabels W.label v.depth).value h} *
        ν {(cavityGeneratedFiniteClockLabels W.label w.depth).value h}) := by
  rw [nativeStreamingGeneratedCrossVertexAtomProgram_measure,
    Measure.map_map measurable_nativeStreamingGeneratedCrossVertexPrefix
      (measurable_nativeStreamingGeneratedCrossVertexAppend W v w)]
  have he : nativeStreamingGeneratedCrossVertexPrefix ∘
      nativeStreamingGeneratedCrossVertexAppend W v w=id :=
    funext (nativeStreamingGeneratedCrossVertexPrefix_append W v w)
  rw [he,Measure.map_id]

theorem nativeStreamingGeneratedCrossVertexAtomProgram_ordered_prefix_law
    (ν : Measure Paper.Overlap) [SFinite ν]
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree) :
    ((nativeStreamingGeneratedCrossVertexAtomProgram
      (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) W v w).measure ν).map
        nativeStreamingGeneratedCrossVertexPrefix=
      ((P.measure ν).restrict (nativeStreamingGeneratedComponentOrderSet W)).withDensity
        (fun h => ν {nativeStreamingGeneratedComponentClock W h v.depth} *
          ν {nativeStreamingGeneratedComponentClock W h w.depth}) := by
  rw [nativeStreamingGeneratedCrossVertexAtomProgram_prefix_law]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (isClosed_nativeStreamingGeneratedComponentOrderSet W).measurableSet]
    with h hh
  rw [nativeStreamingGeneratedComponentClock_eq_label_of_mem W h hh v.depth v.depth_le,
    nativeStreamingGeneratedComponentClock_eq_label_of_mem W h hh w.depth w.depth_le]

theorem nativeStreamingGeneratedCrossVertexComponent_clock_atom_ae
    (ν : Measure Paper.Overlap) [SFinite ν]
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0<v.depth) (hvJ : v.depth<W.depth)
    (hw0 : 0<w.depth) (hwJ : w.depth<W.depth) :
    ∀ᵐ H ∂(nativeStreamingGeneratedCrossVertexAtomProgram P W v w).measure ν,
      nativeStreamingGeneratedComponentClock
        (nativeStreamingGeneratedCrossVertexComponent W v w hv0 hvJ hw0 hwJ) H=
      nativeStreamingGeneratedComponentClock W (nativeStreamingGeneratedCrossVertexPrefix H) := by
  rw [nativeStreamingGeneratedCrossVertexAtomProgram_measure]
  apply (ae_map_iff (measurable_nativeStreamingGeneratedCrossVertexAppend W v w).aemeasurable
    (measurableSet_eq_fun
      (measurable_pi_lambda fun p =>
        (nativeStreamingGeneratedComponentClock_continuous
          (nativeStreamingGeneratedCrossVertexComponent W v w hv0 hvJ hw0 hwJ) p).measurable)
      ((measurable_pi_lambda fun p => (nativeStreamingGeneratedComponentClock_continuous W p).measurable).comp
        measurable_nativeStreamingGeneratedCrossVertexPrefix))).mpr
  exact .of_forall fun h => by
    dsimp only [Function.comp_def]
    rw [nativeStreamingGeneratedCrossVertexPrefix_append,
      nativeStreamingGeneratedCrossVertexComponent_clock_append]

end QuantitativeFollowup
