module
public import QuantitativeFollowup.SupportingGeneratedOriginClockBudget

@[expose] public section

/-! The literal positive clock measure of a native attachment. Its
domination is derived from the real origin integrals and actual fork charges. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def printedGeneratedOriginClockRootMeasure (c : ℝ) (r : Paper.Overlap) : Measure Paper.Overlap :=
  ENNReal.ofReal c • Measure.dirac r

instance printedGeneratedOriginClockRootMeasure_finite (c : ℝ) (r : Paper.Overlap) :
    IsFiniteMeasure (printedGeneratedOriginClockRootMeasure c r) :=
  Measure.smul_finite _ ENNReal.ofReal_ne_top

@[reducible] def printedGeneratedOriginClockMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) :
    {j : ℕ} → FiniteTerminalGenealogy j → ℝ → Measure Paper.Overlap
  | _, .leaf, s => printedGeneratedOriginClockRootMeasure (1-s) (q 0)
  | _, @FiniteTerminalGenealogy.advance j T, s =>
      printedGeneratedOriginClockMeasure μ a q T (Paper.parisiCDF μ (q j)) +
      (parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)) +
      printedGeneratedOriginClockRootMeasure (Paper.parisiCDF μ (q (j+1))-s) (q (j+1))
  | j, .fork T U, s =>
      printedGeneratedOriginClockMeasure μ a q T (Paper.parisiCDF μ (q j)) +
      printedGeneratedOriginClockMeasure μ a q U (Paper.parisiCDF μ (q j)) +
      printedGeneratedOriginClockRootMeasure (2*Paper.parisiCDF μ (q j)-s) (q j)

instance printedGeneratedOriginClockMeasure_finite
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s : ℝ) :
    IsFiniteMeasure (printedGeneratedOriginClockMeasure μ a q T s) := by
  induction T generalizing s with
  | leaf => dsimp only [printedGeneratedOriginClockMeasure]; infer_instance
  | @advance j T ih =>
      haveI := ih (Paper.parisiCDF μ (q j))
      dsimp only [printedGeneratedOriginClockMeasure]
      infer_instance
  | @fork j T U ihT ihU =>
      haveI := ihT (Paper.parisiCDF μ (q j))
      haveI := ihU (Paper.parisiCDF μ (q j))
      dsimp only [printedGeneratedOriginClockMeasure]
      infer_instance

@[reducible] def printedGeneratedOriginForkClockMeasure
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) :
    {j : ℕ} → FiniteTerminalGenealogy j → Measure Paper.Overlap
  | _, .leaf => 0
  | _, .advance T => printedGeneratedOriginForkClockMeasure μ q T
  | j, .fork T U => printedGeneratedOriginForkClockMeasure μ q T +
      printedGeneratedOriginForkClockMeasure μ q U +
      printedGeneratedOriginClockRootMeasure (Paper.parisiCDF μ (q j)) (q j)

instance printedGeneratedOriginForkClockMeasure_finite
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    IsFiniteMeasure (printedGeneratedOriginForkClockMeasure μ q T) := by
  induction T with
  | leaf => dsimp only [printedGeneratedOriginForkClockMeasure]; infer_instance
  | advance T ih => exact ih
  | fork T U ihT ihU =>
      letI := ihT
      letI := ihU
      dsimp only [printedGeneratedOriginForkClockMeasure]
      infer_instance

theorem printedGeneratedClockMeasure_bounded_integrable
    (η : Measure Paper.Overlap) [IsFiniteMeasure η]
    (f : Paper.Overlap → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀r, |f r| ≤ C) :
    Integrable f η := by
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  exact .of_forall (fun r => by simpa only [Real.norm_eq_abs] using hC r)

theorem printedGeneratedOriginClockRootMeasure_integral
    (c : ℝ) (hc : 0 ≤ c) (r : Paper.Overlap) (f : Paper.Overlap → ℝ) :
    (∫x, f x ∂printedGeneratedOriginClockRootMeasure c r) = c*f r := by
  rw [printedGeneratedOriginClockRootMeasure, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal hc, smul_eq_mul]

theorem printedGeneratedOriginClockMeasure_integral
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s : ℝ)
    (hs : s ≤ Paper.parisiCDF μ (q j)) (f : Paper.Overlap → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀r, |f r| ≤ C) :
    (∫r, f r ∂printedGeneratedOriginClockMeasure μ a q T s) =
      nativeStreamingOriginWeightIntegral μ a q T s
        (fun o => f (nativeStreamingOriginLevel q o)) := by
  have hi (η : Measure Paper.Overlap) [IsFiniteMeasure η] : Integrable f η :=
    printedGeneratedClockMeasure_bounded_integrable η f hf C hC
  induction T generalizing s with
  | leaf =>
      have hp : 0 ≤ 1-s := sub_nonneg.mpr (hs.trans (Paper.parisiCDF_le_one μ (q 0)))
      rw [printedGeneratedOriginClockMeasure,
        printedGeneratedOriginClockRootMeasure_integral _ hp]
  | @advance j T ih =>
      simp only [printedGeneratedOriginClockMeasure, nativeStreamingOriginWeightIntegral,
        printedGeneratedOriginLevel_child, nativeStreamingOriginLevel, FiniteCascadeRecordVertex.depth]
      rw [integral_add_measure (hi _) (hi _), integral_add_measure (hi _) (hi _),
        ih _ le_rfl, printedGeneratedOriginClockRootMeasure_integral _ (sub_nonneg.mpr hs)]
  | @fork j T U ihT ihU =>
      have hp : 0 ≤ 2*Paper.parisiCDF μ (q j)-s := by
        linarith [Paper.parisiCDF_nonneg μ (q j)]
      simp only [printedGeneratedOriginClockMeasure, nativeStreamingOriginWeightIntegral,
        printedGeneratedOriginLevel_left, printedGeneratedOriginLevel_right,
        nativeStreamingOriginLevel, FiniteCascadeRecordVertex.depth]
      rw [integral_add_measure (hi _) (hi _), integral_add_measure (hi _) (hi _),
        ihT _ le_rfl, ihU _ le_rfl, printedGeneratedOriginClockRootMeasure_integral _ hp]

theorem printedGeneratedOriginForkClockMeasure_integral
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (f : Paper.Overlap → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀r, |f r| ≤ C) :
    (∫r, f r ∂printedGeneratedOriginForkClockMeasure μ q T) =
      ((printedGeneratedOriginForkDepths T).map (fun d => Paper.parisiCDF μ (q d)*f (q d))).sum := by
  have hi (η : Measure Paper.Overlap) [IsFiniteMeasure η] : Integrable f η :=
    printedGeneratedClockMeasure_bounded_integrable η f hf C hC
  induction T with
  | leaf => simp only [printedGeneratedOriginForkClockMeasure, integral_zero_measure,
      printedGeneratedOriginForkDepths, List.map_nil, List.sum_nil]
  | advance T ih => exact ih
  | @fork j T U ihT ihU =>
      simp only [printedGeneratedOriginForkClockMeasure, printedGeneratedOriginForkDepths,
        List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
      rw [integral_add_measure (hi _) (hi _), integral_add_measure (hi _) (hi _), ihT, ihU,
        printedGeneratedOriginClockRootMeasure_integral _ (Paper.parisiCDF_nonneg μ (q j))]

theorem printedGeneratedOriginClockMeasure_mass
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s : ℝ)
    (hs : s ≤ Paper.parisiCDF μ (q j)) :
    (printedGeneratedOriginClockMeasure μ a q T s).real univ =
      (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ)-s := by
  have h := printedGeneratedOriginClockMeasure_integral μ a q T s hs (fun _ => 1)
    measurable_const 1 (fun _ => by norm_num)
  rw [integral_const, smul_eq_mul, mul_one,
    nativeStreamingOriginWeightIntegral_const μ a ha hμ q hq T s 1, mul_one] at h
  exact h

def printedGeneratedOriginClockMajorant
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) : Measure Paper.Overlap :=
  ENNReal.ofReal (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ) • parisiFreeMeasure μ a +
    printedGeneratedOriginForkClockMeasure μ q T

instance printedGeneratedOriginClockMajorant_finite
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    IsFiniteMeasure (printedGeneratedOriginClockMajorant μ a q T) := by
  haveI : IsFiniteMeasure
      (ENNReal.ofReal (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ) • parisiFreeMeasure μ a) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  dsimp only [printedGeneratedOriginClockMajorant]
  infer_instance

theorem printedGeneratedOriginClockMajorant_integral
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (f : Paper.Overlap → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀r, |f r| ≤ C) :
    (∫r, f r ∂printedGeneratedOriginClockMajorant μ a q T) =
      (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ)*(∫r, f r ∂parisiFreeMeasure μ a) +
      ((printedGeneratedOriginForkDepths T).map (fun d => Paper.parisiCDF μ (q d)*f (q d))).sum := by
  haveI : IsFiniteMeasure
      (ENNReal.ofReal (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ) • parisiFreeMeasure μ a) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hi (η : Measure Paper.Overlap) [IsFiniteMeasure η] : Integrable f η :=
    printedGeneratedClockMeasure_bounded_integrable η f hf C hC
  rw [printedGeneratedOriginClockMajorant, integral_add_measure (hi _) (hi _),
    integral_smul_measure, ENNReal.toReal_ofReal (Nat.cast_nonneg _), smul_eq_mul,
    printedGeneratedOriginForkClockMeasure_integral μ q T f hf C hC]

theorem printedGeneratedOriginClockMeasure_le_majorant
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (hq0 : q 0 = 1) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hqj : q j = zeroOverlap) :
    printedGeneratedOriginClockMeasure μ a q T a ≤ printedGeneratedOriginClockMajorant μ a q T := by
  apply Measure.le_iff.mpr
  intro S hS
  let f : Paper.Overlap → ℝ := S.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hS
  have hC : ∀r, |f r| ≤ 1 := by
    classical
    intro r
    by_cases hr : r ∈ S <;> simp [f, hr]
  have hp : ∀r, 0 ≤ f r := by
    classical
    intro r
    by_cases hr : r ∈ S <;> simp [f, hr]
  have hfi := printedGeneratedClockMeasure_bounded_integrable (parisiFreeMeasure μ a) f hf 1 hC
  have hi := printedGeneratedOriginClockMeasure_integral μ a q T a
    (scalarFloor_cdf_lower hμ (q j).property.1) f hf 1 hC
  have hm := printedGeneratedOriginClockMajorant_integral μ a q T f hf 1 hC
  have hd := printedGeneratedOriginClockBudget μ a ha hμ q hq hq0 T hqj f hfi hp
  have hreal : (printedGeneratedOriginClockMeasure μ a q T a).real S ≤
      (printedGeneratedOriginClockMajorant μ a q T).real S := by
    calc
      _ = ∫r, f r ∂printedGeneratedOriginClockMeasure μ a q T a :=
        (integral_indicator_one hS).symm
      _ = _ := hi
      _ ≤ _ := hd
      _ = _ := hm.symm
      _ = _ := integral_indicator_one hS
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

end QuantitativeFollowup
