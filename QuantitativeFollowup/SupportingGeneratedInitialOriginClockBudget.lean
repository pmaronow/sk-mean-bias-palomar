module
public import QuantitativeFollowup.SupportingGeneratedInitialSiblingErasureGeometry
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionMeasure

@[expose] public section

/-! A unary observation mesh does not increase the initial origin-clock
budget. Actual fork clocks equal the initial mark, and their number is
derived from the true terminal leaf count. No source-law normalization
is inferred from this measure bound. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {J : ℕ}

theorem printedGeneratedInitialForkDepths_at {A : Type*}
    (q : ℕ → A) (p : A) (T : FiniteTerminalGenealogy J)
    (hfork : printedGeneratedInitialForksAt q p T) :
    ∀d ∈ printedGeneratedOriginForkDepths T, q d = p := by
  induction T with
  | leaf => simp [printedGeneratedOriginForkDepths]
  | advance T ih => exact ih hfork
  | @fork j T U ihT ihU =>
      intro d hd
      simp only [printedGeneratedOriginForkDepths, List.mem_append,
        List.mem_singleton] at hd
      rcases hd with (hd | hd) | hd
      · exact ihT hfork.2.1 d hd
      · exact ihU hfork.2.2 d hd
      · subst d
        exact hfork.1

theorem printedGeneratedInitialForkClockMeasure_eq
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) (p : Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (hfork : printedGeneratedInitialForksAt q p T) :
    printedGeneratedOriginForkClockMeasure μ q T =
      (((printedGeneratedOriginForkDepths T).length : ℝ≥0∞) *
        ENNReal.ofReal (Paper.parisiCDF μ p)) • Measure.dirac p := by
  induction T with
  | leaf => simp [printedGeneratedOriginForkClockMeasure, printedGeneratedOriginForkDepths]
  | advance T ih => exact ih hfork
  | @fork j T U ihT ihU =>
      simp only [printedGeneratedOriginForkClockMeasure, printedGeneratedOriginClockRootMeasure,
        hfork.1, ihT hfork.2.1, ihU hfork.2.2]
      rw [←add_smul, ←add_smul]
      congr 1
      simp only [printedGeneratedOriginForkDepths, List.length_append,
        List.length_singleton, Nat.cast_add, Nat.cast_one]
      ring

theorem printedGeneratedInitialOriginClockMeasure_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (hq0 : q 0 = 1) (T : FiniteTerminalGenealogy J) (hqJ : q J = zeroOverlap)
    (p : Paper.Overlap) (hfork : printedGeneratedInitialForksAt q p T) :
    printedGeneratedOriginClockMeasure μ a q T a ≤
      ENNReal.ofReal (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ) •
          parisiFreeMeasure μ a +
        (((FiniteCascadeGenealogy.leafCount (asGenealogy T) - 1 : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Paper.parisiCDF μ p)) • Measure.dirac p := by
  have hcount := printedGeneratedOriginForkDepths_count T
  have hlen : (printedGeneratedOriginForkDepths T).length =
      FiniteCascadeGenealogy.leafCount (asGenealogy T) - 1 := by omega
  have h := printedGeneratedOriginClockMeasure_le_majorant μ a ha hμ q hq hq0 T hqJ
  rw [printedGeneratedOriginClockMajorant,
    printedGeneratedInitialForkClockMeasure_eq μ q p T hfork, hlen] at h
  exact h

theorem printedGeneratedInitialOriginClockMeasure_le_leaf_majorant
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (hq0 : q 0 = 1) (T : FiniteTerminalGenealogy J) (hqJ : q J = zeroOverlap)
    (p : Paper.Overlap) (hfork : printedGeneratedInitialForksAt q p T) :
    printedGeneratedOriginClockMeasure μ a q T a ≤
      ENNReal.ofReal (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ) •
          parisiFreeMeasure μ a +
        ((FiniteCascadeGenealogy.leafCount (asGenealogy T) - 1 : ℕ) : ℝ≥0∞) •
          Measure.dirac p := by
  have hc : ENNReal.ofReal (Paper.parisiCDF μ p) ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal (Paper.parisiCDF_le_one μ p)
  have hb : (((FiniteCascadeGenealogy.leafCount (asGenealogy T) - 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Paper.parisiCDF μ p)) ≤
      ((FiniteCascadeGenealogy.leafCount (asGenealogy T) - 1 : ℕ) : ℝ≥0∞) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc
      (show (0 : ℝ≥0∞) ≤ ((FiniteCascadeGenealogy.leafCount (asGenealogy T) - 1 : ℕ) : ℝ≥0∞)
        from zero_le)
  have hm : (((FiniteCascadeGenealogy.leafCount (asGenealogy T) - 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Paper.parisiCDF μ p)) • Measure.dirac p ≤
      ((FiniteCascadeGenealogy.leafCount (asGenealogy T) - 1 : ℕ) : ℝ≥0∞) • Measure.dirac p := by
    apply Measure.le_iff.mpr
    intro S _
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right hb zero_le
  exact (printedGeneratedInitialOriginClockMeasure_le μ a ha hμ q hq hq0 T hqJ p hfork).trans
    (add_le_add le_rfl hm)

theorem measurable_printedGeneratedOriginSelectionLevel
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J) :
    Measurable (fun g : CavityGeneratedOriginSelection T =>
      nativeStreamingOriginLevel q (cavityGeneratedOriginSelectionOrigin T g)) := by
  change Measurable (Sum.elim
    (fun i => q ((cavityGeneratedOriginForkVertices T).get i).depth)
    (Sum.elim (fun z : Fin (cavityGeneratedOriginEdges T).length × Paper.Overlap => z.2)
      (fun _ : Unit => q J)))
  exact (measurable_of_countable _).sumElim (measurable_snd.sumElim measurable_const)

theorem printedGeneratedOriginSelectionMeasure_clock_map
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq0 : q 0 = 1)
    (T : FiniteTerminalGenealogy J) (s : ℝ) (hs : s ≤ Paper.parisiCDF μ (q J)) :
    (cavityGeneratedOriginSelectionMeasure μ a q T s).map
      (fun g => nativeStreamingOriginLevel q (cavityGeneratedOriginSelectionOrigin T g)) =
      printedGeneratedOriginClockMeasure μ a q T s := by
  classical
  let M := cavityGeneratedOriginSelectionMeasure μ a q T s
  let η := printedGeneratedOriginClockMeasure μ a q T s
  let τ := fun g : CavityGeneratedOriginSelection T =>
    nativeStreamingOriginLevel q (cavityGeneratedOriginSelectionOrigin T g)
  have hm : Measurable τ := measurable_printedGeneratedOriginSelectionLevel q T
  apply Measure.ext
  intro S hS
  let f : Paper.Overlap → ℝ := S.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hS
  have hb : ∀r, |f r| ≤ 1 := by
    intro r
    by_cases hr : r ∈ S <;> simp [f, hr]
  have he := integral_cavityGeneratedOriginSelectionMeasure μ a q hq0 T s hs
    (fun o => f (nativeStreamingOriginLevel q o)) (hf.comp hm) 1 (fun o => hb _)
  have hp := printedGeneratedOriginClockMeasure_integral μ a q T s hs f hf 1 hb
  have hh : (M.map τ).real S = η.real S := by
    calc
      _ = ∫r, f r ∂M.map τ := (integral_indicator_one hS).symm
      _ = ∫g, f (τ g) ∂M := integral_map hm.aemeasurable hf.aestronglyMeasurable
      _ = _ := he
      _ = ∫r, f r ∂η := hp.symm
      _ = _ := integral_indicator_one hS
  have hh' := congrArg ENNReal.ofReal hh
  rw [ofReal_measureReal, ofReal_measureReal] at hh'
  exact hh'

theorem printedGeneratedInitialOriginSelectionMeasure_clock_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (hq0 : q 0 = 1) (T : FiniteTerminalGenealogy J) (hqJ : q J = zeroOverlap)
    (p : Paper.Overlap) (hfork : printedGeneratedInitialForksAt q p T) :
    (cavityGeneratedOriginSelectionMeasure μ a q T a).map
      (fun g => nativeStreamingOriginLevel q (cavityGeneratedOriginSelectionOrigin T g)) ≤
      ENNReal.ofReal (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ) •
          parisiFreeMeasure μ a +
        (((FiniteCascadeGenealogy.leafCount (asGenealogy T) - 1 : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Paper.parisiCDF μ p)) • Measure.dirac p := by
  rw [printedGeneratedOriginSelectionMeasure_clock_map μ a q hq0 T a
    (scalarFloor_cdf_lower hμ (q J).property.1)]
  exact printedGeneratedInitialOriginClockMeasure_le μ a ha hμ q hq hq0 T hqJ p hfork

theorem printedGeneratedInitialOriginSelectionMeasure_clock_le_leaf_majorant
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (hq0 : q 0 = 1) (T : FiniteTerminalGenealogy J) (hqJ : q J = zeroOverlap)
    (p : Paper.Overlap) (hfork : printedGeneratedInitialForksAt q p T) :
    (cavityGeneratedOriginSelectionMeasure μ a q T a).map
      (fun g => nativeStreamingOriginLevel q (cavityGeneratedOriginSelectionOrigin T g)) ≤
      ENNReal.ofReal (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ) •
          parisiFreeMeasure μ a +
        ((FiniteCascadeGenealogy.leafCount (asGenealogy T) - 1 : ℕ) : ℝ≥0∞) • Measure.dirac p := by
  rw [printedGeneratedOriginSelectionMeasure_clock_map μ a q hq0 T a
    (scalarFloor_cdf_lower hμ (q J).property.1)]
  exact printedGeneratedInitialOriginClockMeasure_le_leaf_majorant μ a ha hμ q hq hq0 T hqJ p hfork

end QuantitativeFollowup
