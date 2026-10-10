module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFuturePatternsBranch
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! The genuine atom-plus-inheritance branch is followed by exactly one
restricted free draw. Bounded Fubini and the actual branch prefix law give
the old-prefix weighted future receiver, without current-term attenuation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def nativeStreamingGeneratedSharedFutureProgram
    (μ : Paper.ParisiMeasure) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m) (b : Fin m) (l : ℕ)
    (E : Set (CavityGeneratedHistory Paper.Overlap m × Paper.Overlap)) :
    CavityGeneratedMarkProgram Paper.Overlap ((m+1)+1) :=
  .fresh (cavityGeneratedBranchMarkProgram μ
    (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) b l)
    ((fun z : CavityGeneratedHistory Paper.Overlap (m+1) × Paper.Overlap =>
      (cavityGeneratedHistoryPrefix z.1,z.2)) ⁻¹' E)

theorem nativeStreamingGeneratedSharedFutureProgram_budget
    (μ : Paper.ParisiMeasure) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m) (b : Fin m) (l : ℕ) (hl : 1 ≤ l)
    (E : Set (CavityGeneratedHistory Paper.Overlap m × Paper.Overlap)) :
    (nativeStreamingGeneratedSharedFutureProgram μ P W b l E).budget = l*P.budget := by
  change (cavityGeneratedBranchMarkProgram μ
    (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) b l).budget = _
  rw [cavityGeneratedBranchMarkProgram_budget μ _ b l hl]
  rfl

private theorem sharedFuture_integral_fresh
    (ν : Measure Paper.Overlap) [IsFiniteMeasure ν] (hν : ν univ ≤ 1)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (E : Set (CavityGeneratedHistory Paper.Overlap m × Paper.Overlap)) (hE : MeasurableSet E)
    (G : CavityGeneratedHistory Paper.Overlap (m+1) → ℝ) (hG : Continuous G)
    (C : ℝ) (hC : ∀H, ‖G H‖ ≤ C) :
    (∫H, G H ∂(CavityGeneratedMarkProgram.fresh P E).measure ν) =
      ∫h, ∫r, G (Fin.snoc h r) ∂ν.restrict {r | (h,r) ∈ E} ∂P.measure ν := by
  haveI := P.isFiniteMeasure_measure ν hν
  let g := fun z : CavityGeneratedHistory Paper.Overlap m × Paper.Overlap =>
    G (cavityGeneratedHistoryAppend z)
  have hg : Integrable g ((P.measure ν).prod ν) := by
    apply (integrable_const C).mono'
      (hG.measurable.comp cavityGeneratedHistoryAppend_measurable).aestronglyMeasurable
    exact .of_forall fun z => hC (cavityGeneratedHistoryAppend z)
  change (∫H, G H ∂(((P.measure ν).prod ν).restrict E).map cavityGeneratedHistoryAppend) = _
  rw [integral_map cavityGeneratedHistoryAppend_measurable.aemeasurable hG.aestronglyMeasurable,
    ←integral_indicator hE,integral_prod _ (hg.indicator hE)]
  apply integral_congr_ae
  exact .of_forall fun h => by
    change (∫r, E.indicator g (h,r) ∂ν) =
      ∫r in (Prod.mk h) ⁻¹' E, G (Fin.snoc h r) ∂ν
    rw [←integral_indicator (measurable_prodMk_left hE)]
    rfl

private theorem sharedFuture_measurable_inner
    (ν : Measure Paper.Overlap) [IsFiniteMeasure ν]
    (E : Set (CavityGeneratedHistory Paper.Overlap m × Paper.Overlap)) (hE : MeasurableSet E)
    (G : CavityGeneratedHistory Paper.Overlap (m+1) → ℝ) (hG : Continuous G) :
    Measurable (fun h => ∫r, G (Fin.snoc h r) ∂ν.restrict {r | (h,r) ∈ E}) := by
  have hm := ((hG.measurable.comp cavityGeneratedHistoryAppend_measurable).indicator hE).stronglyMeasurable
  have hi := (hm.integral_prod_right' (ν:=ν)).measurable
  have he : (fun h => ∫r, E.indicator (fun z => G (cavityGeneratedHistoryAppend z)) (h,r) ∂ν) =
      (fun h => ∫r, G (Fin.snoc h r) ∂ν.restrict {r | (h,r) ∈ E}) := by
    funext h
    change (∫r, E.indicator (fun z => G (cavityGeneratedHistoryAppend z)) (h,r) ∂ν) =
      ∫r in (Prod.mk h) ⁻¹' E, G (Fin.snoc h r) ∂ν
    rw [←integral_indicator (measurable_prodMk_left hE)]
    rfl
  exact he ▸ hi

theorem integrable_nativeStreamingGeneratedSharedFutureBranchMoment
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (b : Fin m) (l : ℕ) (E : Set (CavityGeneratedHistory Paper.Overlap m × Paper.Overlap))
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (hF : ∀σ, Continuous (fun h => F h σ))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀h σ, |F h σ| ≤ C) :
    Integrable (nativeStreamingGeneratedSharedFutureBranchMoment D μ a W v e F)
      ((nativeStreamingGeneratedSharedFutureProgram μ P W b l E).measure (parisiFreeMeasure μ a)) := by
  haveI := (nativeStreamingGeneratedSharedFutureProgram μ P W b l E).isFiniteMeasure_measure _
    (cavityGenerated_free_mass_le_one μ a ha)
  apply (integrable_const (2*C)).mono'
    (continuous_nativeStreamingGeneratedSharedFutureBranchMoment D μ a W v e F hF).aestronglyMeasurable
  exact .of_forall fun H => by
    simpa only [Real.norm_eq_abs] using
      nativeStreamingGeneratedSharedFutureBranchMoment_abs_le D μ a W v e F C hC hbound H

theorem nativeStreamingGeneratedSharedFuture_restricted_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (l : ℕ) (hl : 1 ≤ l)
    (E : Set (CavityGeneratedHistory Paper.Overlap m × Paper.Overlap)) (hE : MeasurableSet E)
    (hcell : ∀z ∈ E, nativeStreamingGeneratedComponentClock W z.1 (e.depth+1) ≤ z.2 ∧
      z.2 ≤ nativeStreamingGeneratedComponentClock W z.1 e.depth)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (hF : ∀σ, Continuous (fun h => F h σ))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀h σ, |F h σ| ≤ C) :
    (∫H, nativeStreamingGeneratedSharedFutureBranchMoment D μ a W v e F H
      ∂(nativeStreamingGeneratedSharedFutureProgram μ P W b l E).measure (parisiFreeMeasure μ a)) =
    ∫h, nativeStreamingBranchCharge μ a (nativeStreamingGeneratedComponentClock W h v.depth) l *
      (∫r, nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (F h) (.future (.vertex v) e.depth r)
        ∂(parisiFreeMeasure μ a).restrict {r | (h,r) ∈ E})
      ∂(P.measure (parisiFreeMeasure μ a)).restrict (nativeStreamingGeneratedComponentOrderSet W) := by
  let ν := parisiFreeMeasure μ a
  let B := cavityGeneratedBranchMarkProgram μ
    (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) b l
  let Eb := (fun z : CavityGeneratedHistory Paper.Overlap (m+1) × Paper.Overlap =>
    (cavityGeneratedHistoryPrefix z.1,z.2)) ⁻¹' E
  have hEb : MeasurableSet Eb := hE.preimage
    ((cavityGeneratedHistoryPrefix_measurable.comp measurable_fst).prodMk measurable_snd)
  let G := nativeStreamingGeneratedSharedFutureMoment D μ a W v e F
  have hG : Continuous G := continuous_nativeStreamingGeneratedSharedFutureMoment D μ a W v e F hF
  let A := fun h => ∫r, G (Fin.snoc h r) ∂ν.restrict {r | (h,r) ∈ E}
  have hA : Measurable A := sharedFuture_measurable_inner ν E hE G hG
  have hfirst := sharedFuture_integral_fresh ν (cavityGenerated_free_mass_le_one μ a ha)
    B Eb hEb (nativeStreamingGeneratedSharedFutureBranchMoment D μ a W v e F)
    (continuous_nativeStreamingGeneratedSharedFutureBranchMoment D μ a W v e F hF) (2*C)
    (fun H => by simpa only [Real.norm_eq_abs] using
      nativeStreamingGeneratedSharedFutureBranchMoment_abs_le D μ a W v e F C hC hbound H)
  change (∫H, nativeStreamingGeneratedSharedFutureBranchMoment D μ a W v e F H
    ∂(CavityGeneratedMarkProgram.fresh B Eb).measure ν) = _
  rw [hfirst]
  have herase : (fun H => ∫r, nativeStreamingGeneratedSharedFutureBranchMoment D μ a W v e F
      (Fin.snoc H r) ∂ν.restrict {r | (H,r) ∈ Eb}) =
      (fun H => A (cavityGeneratedHistoryPrefix H)) := by
    funext H
    simp only [nativeStreamingGeneratedSharedFutureBranchMoment,
      nativeStreamingGeneratedSharedFutureHistoryEraseBranch_snoc]
    rfl
  rw [herase,←integral_map cavityGeneratedHistoryPrefix_measurable.aemeasurable hA.aestronglyMeasurable,
    nativeStreamingGeneratedVertexBranchProgram_ordered_prefix_law μ a P W v b hb l hl]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_nativeStreamingGeneratedVertexBranchCharge μ a W v l).ennreal_ofReal
    (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (isClosed_nativeStreamingGeneratedComponentOrderSet W).measurableSet]
    with h hh
  rw [ENNReal.toReal_ofReal (nativeStreamingGeneratedVertexBranchCharge_nonneg μ a _ l hl)]
  simp only [smul_eq_mul]
  apply congrArg (fun z : ℝ =>
    nativeStreamingBranchCharge μ a (nativeStreamingGeneratedComponentClock W h v.depth) l * z)
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurable_prodMk_left hE)] with r hr
  exact nativeStreamingGeneratedSharedFutureMoment_snoc D μ a W v e F h r hh (hcell (h,r) hr)

end QuantitativeFollowup
