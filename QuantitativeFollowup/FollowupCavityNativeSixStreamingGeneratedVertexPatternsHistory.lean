module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexPatternsMoments

@[expose] public section

/-! Integrating the actual enlarged component against its generated atom
history gives the true singleton-weighted original history integral. The
ordered receiver derives its physical atom clock from the restriction. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem measurable_nativeStreamingGeneratedAtomMass
    (ν : Measure Paper.Overlap) [SFinite ν]
    (q : CavityGeneratedHistory Paper.Overlap m → Paper.Overlap) (hq : Measurable q) :
    Measurable (fun h => ν {q h}) := by
  have hs : MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m × Paper.Overlap |
      z.2=q z.1} := measurableSet_eq_fun measurable_snd (hq.comp measurable_fst)
  convert measurable_measure_prodMk_left (ν:=ν) hs using 1
  funext h
  congr 1

theorem nativeStreamingGeneratedVertexMoment_atom_ae
    (ν : Measure Paper.Overlap) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < W.depth) (k : NativeStreamingGeneratedVertexKind)
    (G : CavityGeneratedHistory Paper.Overlap m →
      TerminalSpins (Configuration n) W.tree × k.Mark (Configuration n) → ℝ) :
    (fun H => nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ k) H)
        W.tree v k (G (cavityGeneratedHistoryPrefix H))) =ᵐ[
          (nativeStreamingGeneratedVertexAtomProgram P W v).measure ν]
    (fun H => nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock W (cavityGeneratedHistoryPrefix H))
        W.tree v k (G (cavityGeneratedHistoryPrefix H))) := by
  filter_upwards [nativeStreamingGeneratedVertexComponent_clock_consistent ν P W v hv0 hvJ k] with H hH
  rw [hH]

theorem nativeStreamingGeneratedVertexMoment_atom_integral
    (ν : Measure Paper.Overlap) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < W.depth) (k : NativeStreamingGeneratedVertexKind)
    (G : CavityGeneratedHistory Paper.Overlap m →
      TerminalSpins (Configuration n) W.tree × k.Mark (Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun h => G h σ)) :
    (∫ H, nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ k) H)
        W.tree v k (G (cavityGeneratedHistoryPrefix H))
      ∂(nativeStreamingGeneratedVertexAtomProgram P W v).measure ν) =
    ∫ h, nativeStreamingGeneratedVertexMoment D μ a (nativeStreamingGeneratedComponentClock W h)
      W.tree v k (G h)
      ∂(P.measure ν).withDensity
        (fun h => ν {(cavityGeneratedFiniteClockLabels W.label v.depth).value h}) := by
  rw [integral_congr_ae (nativeStreamingGeneratedVertexMoment_atom_ae ν P D μ a W v hv0 hvJ k G)]
  have hc := continuous_nativeStreamingGeneratedVertexMoment D μ a W v k G hG
  rw [←integral_map cavityGeneratedHistoryPrefix_measurable.aemeasurable hc.aestronglyMeasurable,
    nativeStreamingGeneratedVertexAtomProgram_prefix_law]

theorem integrable_nativeStreamingGeneratedVertexMoment_atom
    (ν : Measure Paper.Overlap) [SFinite ν] (hν : ν univ ≤ 1)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < W.depth) (k : NativeStreamingGeneratedVertexKind)
    (G : CavityGeneratedHistory Paper.Overlap m →
      TerminalSpins (Configuration n) W.tree × k.Mark (Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun h => G h σ))
    (C : ℝ) (hC : ∀h σ, |G h σ| ≤ C) :
    Integrable (fun H => nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ k) H)
        W.tree v k (G (cavityGeneratedHistoryPrefix H)))
      ((nativeStreamingGeneratedVertexAtomProgram P W v).measure ν) := by
  haveI := (nativeStreamingGeneratedVertexAtomProgram P W v).isFiniteMeasure_measure ν hν
  have hc := continuous_nativeStreamingGeneratedVertexMoment D μ a W v k G hG
  have he := nativeStreamingGeneratedVertexMoment_atom_ae ν P D μ a W v hv0 hvJ k G
  have hm := (hc.measurable.comp cavityGeneratedHistoryPrefix_measurable).aestronglyMeasurable.congr he.symm
  apply (integrable_const C).mono' hm
  exact .of_forall fun H => by
    simpa only [Real.norm_eq_abs] using nativeStreamingGeneratedVertexMoment_abs_le D μ a _
      W.tree v k (G (cavityGeneratedHistoryPrefix H)) C (hC _)

theorem nativeStreamingGeneratedVertexAtomProgram_ordered_prefix_law
    (ν : Measure Paper.Overlap) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree) :
    ((nativeStreamingGeneratedVertexAtomProgram
      (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) W v).measure ν).map
        cavityGeneratedHistoryPrefix =
      ((P.measure ν).restrict (nativeStreamingGeneratedComponentOrderSet W)).withDensity
        (fun h => ν {nativeStreamingGeneratedComponentClock W h v.depth}) := by
  rw [nativeStreamingGeneratedVertexAtomProgram_prefix_law]
  change ((P.measure ν).restrict (nativeStreamingGeneratedComponentOrderSet W)).withDensity _ = _
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (isClosed_nativeStreamingGeneratedComponentOrderSet W).measurableSet]
    with h hh
  rw [nativeStreamingGeneratedComponentClock_eq_label_of_mem W h hh v.depth v.depth_le]

theorem nativeStreamingGeneratedVertexMoment_ordered_atom_integral
    (ν : Measure Paper.Overlap) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < W.depth) (k : NativeStreamingGeneratedVertexKind)
    (G : CavityGeneratedHistory Paper.Overlap m →
      TerminalSpins (Configuration n) W.tree × k.Mark (Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun h => G h σ)) :
    (∫ H, nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ k) H)
        W.tree v k (G (cavityGeneratedHistoryPrefix H))
      ∂(nativeStreamingGeneratedVertexAtomProgram
        (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) W v).measure ν) =
    ∫ h, nativeStreamingGeneratedVertexMoment D μ a (nativeStreamingGeneratedComponentClock W h)
      W.tree v k (G h)
      ∂((P.measure ν).restrict (nativeStreamingGeneratedComponentOrderSet W)).withDensity
        (fun h => ν {nativeStreamingGeneratedComponentClock W h v.depth}) := by
  rw [integral_congr_ae (nativeStreamingGeneratedVertexMoment_atom_ae ν
    (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) D μ a W v hv0 hvJ k G)]
  have hc := continuous_nativeStreamingGeneratedVertexMoment D μ a W v k G hG
  rw [←integral_map cavityGeneratedHistoryPrefix_measurable.aemeasurable hc.aestronglyMeasurable,
    nativeStreamingGeneratedVertexAtomProgram_ordered_prefix_law]

theorem nativeStreamingGeneratedVertexMoment_ordered_atom_receiver
    (ν : Measure Paper.Overlap) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < W.depth) (k : NativeStreamingGeneratedVertexKind)
    (G : (ℕ → Paper.Overlap) →
      TerminalSpins (Configuration n) W.tree × k.Mark (Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun h => G (nativeStreamingGeneratedComponentClock W h) σ)) :
    (∫ H, nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ k) H)
      W.tree v k
      (G (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ k) H))
      ∂(nativeStreamingGeneratedVertexAtomProgram
        (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) W v).measure ν) =
    ∫ h, nativeStreamingGeneratedVertexMoment D μ a (nativeStreamingGeneratedComponentClock W h)
      W.tree v k (G (nativeStreamingGeneratedComponentClock W h))
      ∂((P.measure ν).restrict (nativeStreamingGeneratedComponentOrderSet W)).withDensity
        (fun h => ν {nativeStreamingGeneratedComponentClock W h v.depth}) := by
  calc
    _ = ∫ H, nativeStreamingGeneratedVertexMoment D μ a
        (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ k) H)
        W.tree v k (G (nativeStreamingGeneratedComponentClock W (cavityGeneratedHistoryPrefix H)))
        ∂(nativeStreamingGeneratedVertexAtomProgram
          (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) W v).measure ν := by
      apply integral_congr_ae
      filter_upwards [nativeStreamingGeneratedVertexComponent_clock_consistent ν
        (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) W v hv0 hvJ k] with H hH
      rw [hH]
    _ = _ := nativeStreamingGeneratedVertexMoment_ordered_atom_integral ν P D μ a W v hv0 hvJ k
      (fun h => G (nativeStreamingGeneratedComponentClock W h)) hG

theorem integrable_nativeStreamingGeneratedVertexMoment_ordered_atom_receiver
    (ν : Measure Paper.Overlap) [SFinite ν] (hν : ν univ ≤ 1)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < W.depth) (k : NativeStreamingGeneratedVertexKind)
    (G : (ℕ → Paper.Overlap) →
      TerminalSpins (Configuration n) W.tree × k.Mark (Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun h => G (nativeStreamingGeneratedComponentClock W h) σ))
    (C : ℝ) (hC : ∀q σ, |G q σ| ≤ C) :
    Integrable (fun H => nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ k) H)
      W.tree v k
      (G (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ k) H)))
      ((nativeStreamingGeneratedVertexAtomProgram
        (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) W v).measure ν) := by
  have hi := integrable_nativeStreamingGeneratedVertexMoment_atom ν hν
    (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) D μ a W v hv0 hvJ k
    (fun h => G (nativeStreamingGeneratedComponentClock W h)) hG C
    (fun h σ => hC (nativeStreamingGeneratedComponentClock W h) σ)
  apply hi.congr
  filter_upwards [nativeStreamingGeneratedVertexComponent_clock_consistent ν
    (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) W v hv0 hvJ k] with H hH
  rw [hH]

theorem nativeStreamingGeneratedVertexMoment_ordered_atom_receiver_real
    (ν : Measure Paper.Overlap) [IsFiniteMeasure ν]
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < W.depth) (k : NativeStreamingGeneratedVertexKind)
    (G : (ℕ → Paper.Overlap) →
      TerminalSpins (Configuration n) W.tree × k.Mark (Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun h => G (nativeStreamingGeneratedComponentClock W h) σ)) :
    (∫ H, nativeStreamingGeneratedVertexMoment D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ k) H)
      W.tree v k
      (G (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ k) H))
      ∂(nativeStreamingGeneratedVertexAtomProgram
        (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) W v).measure ν) =
    ∫ h, ν.real {nativeStreamingGeneratedComponentClock W h v.depth} *
      nativeStreamingGeneratedVertexMoment D μ a (nativeStreamingGeneratedComponentClock W h)
      W.tree v k (G (nativeStreamingGeneratedComponentClock W h))
      ∂(P.measure ν).restrict (nativeStreamingGeneratedComponentOrderSet W) := by
  rw [nativeStreamingGeneratedVertexMoment_ordered_atom_receiver ν P D μ a W v hv0 hvJ k G hG]
  have hm := measurable_nativeStreamingGeneratedAtomMass ν
    (fun h => nativeStreamingGeneratedComponentClock W h v.depth)
    (nativeStreamingGeneratedComponentClock_continuous W v.depth).measurable
  simpa only [Measure.real,smul_eq_mul] using
    integral_withDensity_eq_integral_toReal_smul hm
      (.of_forall fun h => measure_lt_top ν {nativeStreamingGeneratedComponentClock W h v.depth})
      (fun h => nativeStreamingGeneratedVertexMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree v k (G (nativeStreamingGeneratedComponentClock W h)))

end QuantitativeFollowup
