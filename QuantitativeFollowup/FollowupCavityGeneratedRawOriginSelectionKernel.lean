module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionKernel
public import QuantitativeFollowup.SupportingGeneratedInitialOriginClockBudget

@[expose] public section

/-! The actual raw selected-origin kernel needs measurable physical
clocks, not a label for every unary observation. Actual source support
will supply antitonicity and endpoint clocks; only genuine fork clocks
are routed to inherited marks in the subsequent budget adapter. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
variable {H : Type*} [MeasurableSpace H] {J : ℕ}

def cavityGeneratedRawOriginSelectionClock
    (q : H → ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (z : H × CavityGeneratedOriginSelection T) : Paper.Overlap :=
  nativeStreamingOriginLevel (q z.1) (cavityGeneratedOriginSelectionOrigin T z.2)

theorem measurable_cavityGeneratedRawOriginSelectionClock
    (q : H → ℕ → Paper.Overlap) (hq : ∀d, Measurable (fun h => q h d))
    (T : FiniteTerminalGenealogy J) :
    Measurable (cavityGeneratedRawOriginSelectionClock q T) := by
  let A := Fin (cavityGeneratedOriginForkVertices T).length
  let B := Fin (cavityGeneratedOriginEdges T).length × Paper.Overlap
  have hf : Measurable (fun z : H × A =>
      q z.1 ((cavityGeneratedOriginForkVertices T).get z.2).depth) :=
    measurable_from_prod_countable_left (fun i => by
      change Measurable (fun h : H =>
        q h ((cavityGeneratedOriginForkVertices T).get i).depth)
      exact hq _)
  have he : Measurable (fun z : H × B => z.2.2) := measurable_snd.comp measurable_snd
  have hr : Measurable (fun z : H × Unit => q z.1 J) :=
    (hq _).comp measurable_fst
  have hinner := (he.sumElim hr).comp (MeasurableEquiv.prodSumDistrib H B Unit).measurable
  have houter := (hf.sumElim hinner).comp
    (MeasurableEquiv.prodSumDistrib H A (B ⊕ Unit)).measurable
  convert houter using 1
  funext z
  rcases z with ⟨h,g⟩
  cases g with
  | inl i => rfl
  | inr g => cases g <;> rfl

theorem measurable_cavityGeneratedRawOriginSelectionMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : H → ℕ → Paper.Overlap) (hq : ∀d, Measurable (fun h => q h d))
    (T : FiniteTerminalGenealogy J) :
    Measurable (fun h : H => cavityGeneratedOriginSelectionMeasure μ a (q h) T a) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have hc (d : ℕ) : Measurable (fun h : H =>
      Paper.parisiCDF μ (q h d)) :=
    (Paper.parisiCDF_measurable μ).comp
      (measurable_subtype_coe.comp (hq d))
  have hf (i : Fin (cavityGeneratedOriginForkVertices T).length) :
      Measurable (fun h : H =>
        ENNReal.ofReal (Paper.parisiCDF μ
          (q h ((cavityGeneratedOriginForkVertices T).get i).depth))*
            Measure.dirac (Sum.inl i : CavityGeneratedOriginSelection T) S) :=
    (hc _).ennreal_ofReal.mul measurable_const
  have he (i : Fin (cavityGeneratedOriginEdges T).length) :
      Measurable (fun h : H =>
        (((parisiFreeMeasure μ a).restrict
          (Ioc (q h (((cavityGeneratedOriginEdges T).get i).depth+1))
            (q h ((cavityGeneratedOriginEdges T).get i).depth))).map
              (cavityGeneratedOriginSelectionEdge T i)) S) := by
    let E := cavityGeneratedOriginSelectionEdge T i ⁻¹' S
    have hE : MeasurableSet E := (measurable_cavityGeneratedOriginSelectionEdge _ i) hS
    let f : Paper.Overlap → ℝ := E.indicator (fun _ => 1)
    have hfi : Measurable f := measurable_const.indicator hE
    have hm := measurable_cavityGeneratedMovingCellIntegral (parisiFreeMeasure μ a)
      (fun h => q h (((cavityGeneratedOriginEdges T).get i).depth+1))
      (fun h => q h ((cavityGeneratedOriginEdges T).get i).depth)
      (hq _)
      (hq _) f hfi
    have hh (h : H) :
        ENNReal.ofReal (∫r in
          Ioc (q h (((cavityGeneratedOriginEdges T).get i).depth+1))
            (q h ((cavityGeneratedOriginEdges T).get i).depth),
          f r ∂parisiFreeMeasure μ a) =
        (((parisiFreeMeasure μ a).restrict
          (Ioc (q h (((cavityGeneratedOriginEdges T).get i).depth+1))
            (q h ((cavityGeneratedOriginEdges T).get i).depth))).map
              (cavityGeneratedOriginSelectionEdge T i)) S := by
      rw [Measure.map_apply (measurable_cavityGeneratedOriginSelectionEdge _ i) hS]
      change ENNReal.ofReal (∫r,f r ∂(parisiFreeMeasure μ a).restrict
        (Ioc (q h (((cavityGeneratedOriginEdges T).get i).depth+1))
          (q h ((cavityGeneratedOriginEdges T).get i).depth))) =
        ((parisiFreeMeasure μ a).restrict
          (Ioc (q h (((cavityGeneratedOriginEdges T).get i).depth+1))
            (q h ((cavityGeneratedOriginEdges T).get i).depth))) E
      rw [show f = E.indicator (1 : Paper.Overlap → ℝ) from rfl,
        integral_indicator_one hE, ofReal_measureReal]
    exact (funext hh) ▸ hm.ennreal_ofReal
  have hr : Measurable (fun h : H =>
      ENNReal.ofReal (Paper.parisiCDF μ (q h J)-a)*
        Measure.dirac (Sum.inr (Sum.inr ()) : CavityGeneratedOriginSelection T) S) :=
    ((hc _).sub measurable_const).ennreal_ofReal.mul measurable_const
  have hm := ((Finset.measurable_fun_sum Finset.univ (fun i _ => hf i)).add
    (Finset.measurable_fun_sum Finset.univ (fun i _ => he i))).add hr
  convert hm using 1
  funext h
  simp only [Pi.add_apply,cavityGeneratedOriginSelectionMeasure, Measure.add_apply,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]

def cavityGeneratedRawOriginSelectionKernel
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : H → ℕ → Paper.Overlap) (hq : ∀d, Measurable (fun h => q h d))
    (T : FiniteTerminalGenealogy J) : Kernel H (CavityGeneratedOriginSelection T) where
  toFun h := cavityGeneratedOriginSelectionMeasure μ a (q h) T a
  measurable' := measurable_cavityGeneratedRawOriginSelectionMeasure μ a q hq T

theorem cavityGeneratedRawOriginSelectionKernel_apply
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : H → ℕ → Paper.Overlap) (hq : ∀d, Measurable (fun h => q h d))
    (T : FiniteTerminalGenealogy J) (h : H) :
    cavityGeneratedRawOriginSelectionKernel μ a q hq T h =
      cavityGeneratedOriginSelectionMeasure μ a (q h) T a := rfl

theorem cavityGeneratedRawOriginSelectionKernel_clock_map
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : H → ℕ → Paper.Overlap) (hq : ∀d, Measurable (fun h => q h d))
    (T : FiniteTerminalGenealogy J) (h : H) (hzero : q h 0 = 1)
    (hs : a ≤ Paper.parisiCDF μ (q h J)) :
    (cavityGeneratedRawOriginSelectionKernel μ a q hq T h).map
      (fun g => cavityGeneratedRawOriginSelectionClock q T (h,g)) =
      printedGeneratedOriginClockMeasure μ a (q h) T a :=
  printedGeneratedOriginSelectionMeasure_clock_map μ a (q h) hzero T a hs

theorem rawOriginSelection_global_mass_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) :
    cavityGeneratedOriginSelectionMeasure μ a q T a univ ≤
      ((cavityGeneratedOriginForkVertices T).length : ℝ≥0∞) +
      ((cavityGeneratedOriginEdges T).length : ℝ≥0∞) * (parisiFreeMeasure μ a) univ +
      ENNReal.ofReal (1-a) := by
  classical
  have hf (i : Fin (cavityGeneratedOriginForkVertices T).length) :
      ENNReal.ofReal (Paper.parisiCDF μ (q ((cavityGeneratedOriginForkVertices T).get i).depth)) ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal (Paper.parisiCDF_le_one μ _)
  have he (i : Fin (cavityGeneratedOriginEdges T).length) :
      (((parisiFreeMeasure μ a).restrict
        (Ioc (q (((cavityGeneratedOriginEdges T).get i).depth+1))
          (q ((cavityGeneratedOriginEdges T).get i).depth))).map
            (cavityGeneratedOriginSelectionEdge T i)) univ ≤ (parisiFreeMeasure μ a) univ := by
    rw [Measure.map_apply (measurable_cavityGeneratedOriginSelectionEdge T i) MeasurableSet.univ,
      preimage_univ]
    exact Measure.restrict_le_self univ
  have hr : ENNReal.ofReal (Paper.parisiCDF μ (q J)-a) ≤ ENNReal.ofReal (1-a) :=
    ENNReal.ofReal_le_ofReal (sub_le_sub_right (Paper.parisiCDF_le_one μ _) a)
  simp only [cavityGeneratedOriginSelectionMeasure, Measure.add_apply,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem,
    mem_univ, mul_one]
  have hfs : (∑ i : Fin (cavityGeneratedOriginForkVertices T).length,
      ENNReal.ofReal (Paper.parisiCDF μ (q ((cavityGeneratedOriginForkVertices T).get i).depth))) ≤
      ((cavityGeneratedOriginForkVertices T).length : ℝ≥0∞) := by
    calc
      _ ≤ ∑ _i : Fin (cavityGeneratedOriginForkVertices T).length, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun i _ => hf i
      _ = _ := by simp
  have hes : (∑ i : Fin (cavityGeneratedOriginEdges T).length,
      (((parisiFreeMeasure μ a).restrict
        (Ioc (q (((cavityGeneratedOriginEdges T).get i).depth+1))
          (q ((cavityGeneratedOriginEdges T).get i).depth))).map
            (cavityGeneratedOriginSelectionEdge T i)) univ) ≤
      ((cavityGeneratedOriginEdges T).length : ℝ≥0∞) * (parisiFreeMeasure μ a) univ := by
    calc
      _ ≤ ∑ _i : Fin (cavityGeneratedOriginEdges T).length, (parisiFreeMeasure μ a) univ :=
        Finset.sum_le_sum fun i _ => he i
      _ = _ := by simp [nsmul_eq_mul]
  exact add_le_add (add_le_add hfs hes) hr

instance cavityGeneratedRawOriginSelectionKernel_finite
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : H → ℕ → Paper.Overlap) (hq : ∀d, Measurable (fun h => q h d))
    (T : FiniteTerminalGenealogy J) :
    IsFiniteKernel (cavityGeneratedRawOriginSelectionKernel μ a q hq T) where
  exists_univ_le := ⟨_, by
    apply lt_top_iff_ne_top.mpr
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.natCast_ne_top _, ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (measure_ne_top _ _)⟩, ENNReal.ofReal_ne_top⟩,
    fun h => rawOriginSelection_global_mass_le μ a (q h) T⟩

end QuantitativeFollowup
