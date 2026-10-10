module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginClockIntegrals
public import QuantitativeFollowup.SupportingGeneratedOriginClockMeasure
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! The actual moving clock kernel of a generated component. Its
measurability, mass and inherited-coordinate domination are derived from
the native origin measure and the genuine construction witnesses. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
variable {m : ℕ}

theorem measurable_cavityGeneratedOriginClockMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ ∈ scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    Measurable (fun h : CavityGeneratedHistory Paper.Overlap m =>
      printedGeneratedOriginClockMeasure μ a (W.clockTemplate.clock h c) (W.tree c) a) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  let f : Paper.Overlap → ℝ := S.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hS
  have hb : ∀r, |f r| ≤ 1 := by
    classical
    intro r
    by_cases hr : r ∈ S <;> simp [f, hr]
  have hm := measurable_cavityGeneratedOriginClockIntegral μ a
    (fun h => W.clockTemplate.clock h c)
    (fun d => (W.clockTemplate.clock_continuous c d).measurable)
    (W.tree c) (fun _ => a) measurable_const f hf
  have he (h : CavityGeneratedHistory Paper.Overlap m) :
      ENNReal.ofReal (nativeStreamingOriginWeightIntegral μ a
        (W.clockTemplate.clock h c) (W.tree c) a
        (fun o => f (nativeStreamingOriginLevel (W.clockTemplate.clock h c) o))) =
      printedGeneratedOriginClockMeasure μ a
        (W.clockTemplate.clock h c) (W.tree c) a S := by
    have hs : a ≤ Paper.parisiCDF μ (W.clockTemplate.clock h c (W.depth c)) := by
      let c' : Fin W.clockTemplate.componentCount := c
      change a ≤ Paper.parisiCDF μ (W.clockTemplate.clock h c' (W.clockTemplate.depth c'))
      rw [W.clockTemplate.clock_initial h c']
      exact scalarFloor_cdf_lower hμ (by norm_num)
    rw [←printedGeneratedOriginClockMeasure_integral μ a _ (W.tree c) a hs f hf 1 hb]
    rw [show f = S.indicator (1 : Paper.Overlap → ℝ) from rfl,
      integral_indicator_one hS, ofReal_measureReal]
  exact (funext he) ▸ hm.ennreal_ofReal

def cavityGeneratedOriginClockKernel
    (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ ∈ scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    Kernel (CavityGeneratedHistory Paper.Overlap m) Paper.Overlap where
  toFun h := printedGeneratedOriginClockMeasure μ a
    (W.clockTemplate.clock h c) (W.tree c) a
  measurable' := measurable_cavityGeneratedOriginClockMeasure μ a hμ W c

theorem cavityGeneratedOriginClockKernel_apply
    (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ ∈ scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    cavityGeneratedOriginClockKernel μ a hμ W c h =
      printedGeneratedOriginClockMeasure μ a
        (W.clockTemplate.clock h c) (W.tree c) a := rfl

theorem cavityGeneratedOriginClockKernel_mass
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m) :
    (cavityGeneratedOriginClockKernel μ a hμ W c h).real univ =
      (FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ)-a := by
  have hs : a ≤ Paper.parisiCDF μ (W.clockTemplate.clock h c (W.depth c)) := by
    let c' : Fin W.clockTemplate.componentCount := c
    change a ≤ Paper.parisiCDF μ (W.clockTemplate.clock h c' (W.clockTemplate.depth c'))
    rw [W.clockTemplate.clock_initial h c']
    exact scalarFloor_cdf_lower hμ (by norm_num)
  exact printedGeneratedOriginClockMeasure_mass μ a ha hμ _
    (antitone_nat_of_succ_le (fun d => W.clockTemplate.clock_step_le h c d))
    (W.tree c) a hs

theorem cavityGeneratedOriginClockKernel_mass_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m) :
    cavityGeneratedOriginClockKernel μ a hμ W c h univ ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) := by
  haveI : IsFiniteMeasure (cavityGeneratedOriginClockKernel μ a hμ W c h) :=
    printedGeneratedOriginClockMeasure_finite μ a _ (W.tree c) a
  rw [←ofReal_measureReal, cavityGeneratedOriginClockKernel_mass μ a ha hμ W c h]
  exact (ENNReal.ofReal_le_ofReal (sub_le_self _ ha.1)).trans_eq (by simp)

theorem cavityGeneratedOriginClockKernel_finite
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) :
    IsFiniteKernel (cavityGeneratedOriginClockKernel μ a hμ W c) where
  exists_univ_le := ⟨_, ENNReal.natCast_lt_top _,
    cavityGeneratedOriginClockKernel_mass_le μ a ha hμ W c⟩

theorem cavityGeneratedOriginForkClockMeasure_eq_depths
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    printedGeneratedOriginForkClockMeasure μ q T =
      ((printedGeneratedOriginForkDepths T).map
        (fun d => printedGeneratedOriginClockRootMeasure (Paper.parisiCDF μ (q d)) (q d))).sum := by
  induction T with
  | leaf => simp only [printedGeneratedOriginForkClockMeasure,
      printedGeneratedOriginForkDepths, List.map_nil, List.sum_nil]
  | advance T ih => exact ih
  | fork T U ihT ihU =>
      simp only [printedGeneratedOriginForkClockMeasure, printedGeneratedOriginForkDepths,
        List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, ihT, ihU]

theorem cavityGeneratedOriginForkClockMeasure_eq_history
    (μ : Paper.ParisiMeasure) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ W.clockTemplate.orderSet) :
    printedGeneratedOriginForkClockMeasure μ (W.clockTemplate.clock h c) (W.tree c) =
      ((cavityGeneratedOriginForkMarks W c).map
        (fun i => printedGeneratedOriginClockRootMeasure (Paper.parisiCDF μ (h i)) (h i))).sum := by
  rw [cavityGeneratedOriginForkClockMeasure_eq_depths]
  let L := printedGeneratedOriginForkDepths (W.tree c)
  let A := fun d => printedGeneratedOriginClockRootMeasure
    (Paper.parisiCDF μ (W.clockTemplate.clock h c d)) (W.clockTemplate.clock h c d)
  let B := fun i => printedGeneratedOriginClockRootMeasure (Paper.parisiCDF μ (h i)) (h i)
  have he : L.map A = (cavityGeneratedOriginForkMarks W c).map B := by
    calc
      L.map A = (L.attach.map Subtype.val).map A :=
        congrArg (List.map A) (List.attach_map_subtype_val L).symm
      _ = L.attach.map (fun d => A d.val) := by rw [List.map_map]; rfl
      _ = L.attach.map (fun d => B (cavityGeneratedOriginForkMark W c d)) := by
        apply List.map_congr_left
        intro d _
        dsimp only [A, B]
        rw [cavityGeneratedOriginForkMark_clock W c d h hh]
      _ = (cavityGeneratedOriginForkMarks W c).map B := by
        simp only [cavityGeneratedOriginForkMarks, List.map_map, Function.comp_def, L]
  exact congrArg List.sum he

theorem cavityGeneratedOriginClockKernel_le_history_marks
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ W.clockTemplate.orderSet) :
    cavityGeneratedOriginClockKernel μ a hμ W c h ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) • parisiFreeMeasure μ a +
        ∑j : Fin (cavityGeneratedOriginForkMarks W c).length,
          Measure.dirac (h ((cavityGeneratedOriginForkMarks W c).get j)) := by
  have hd := printedGeneratedOriginClockMeasure_le_majorant μ a ha hμ
    (W.clockTemplate.clock h c)
    (antitone_nat_of_succ_le (fun d => W.clockTemplate.clock_step_le h c d))
    (W.clockTemplate.clock_terminal h c) (W.tree c) (W.clockTemplate.clock_initial h c)
  rw [printedGeneratedOriginClockMajorant,
    cavityGeneratedOriginForkClockMeasure_eq_history μ W c h hh] at hd
  simp only [ENNReal.ofReal_natCast] at hd
  apply hd.trans
  apply add_le_add_right
  let L := cavityGeneratedOriginForkMarks W c
  have he (f : Fin m → Measure Paper.Overlap) :
      (L.map f).sum = ∑j : Fin L.length, f (L.get j) := by
    have hh := congrArg (fun A : List (Fin m) => (A.map f).sum) (List.ofFn_get L)
    simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_def] using hh.symm
  rw [he]
  apply Finset.sum_le_sum
  intro j _
  unfold printedGeneratedOriginClockRootMeasure
  exact (cavityGenerated_smul_mono (Measure.dirac (h (L.get j)))
    ((ENNReal.ofReal_le_ofReal (Paper.parisiCDF_le_one μ (h (L.get j)))).trans_eq (by simp))).trans_eq
      (one_smul _ _)

end QuantitativeFollowup
