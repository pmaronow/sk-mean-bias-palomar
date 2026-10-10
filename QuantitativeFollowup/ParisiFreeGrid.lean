module
public import QuantitativeFollowup.ParisiFreeMeasure
public import QuantitativePaper.VectorProfileMeasure
public import FourPapersCommon.ParisiCDFRight

@[expose] public section

/-! Upward finite-grid approximation retains the prescribed atom at zero
and transports the actual free Stieltjes measure exactly. -/
noncomputable section
open Set MeasureTheory QuantitativePaper FourPapersCommon
open scoped ENNReal
namespace QuantitativeFollowup

theorem parisiGridRound_zero (n : ℕ) :
    Paper.parisiGridRound n zeroOverlap=zeroOverlap := by
  apply Subtype.ext
  simp [Paper.parisiGridRound,Paper.parisiGridPoint,Paper.parisiGridIndex,zeroOverlap]

theorem parisiGridMeasure_root_mass (μ : Paper.ParisiMeasure) (n : ℕ) :
    zeroMass (Paper.parisiGridMeasure μ n)=zeroMass μ := by
  rw [zeroMass_eq_parisiCDF_zero,zeroMass_eq_parisiCDF_zero]
  have he:=parisiCDF_grid_at_round μ n zeroOverlap
  rw [parisiGridRound_zero] at he
  exact he

theorem parisiGridMeasure_mem_scalarFloor (μ : Paper.ParisiMeasure) (s : ℝ)
    (hμ : μ∈scalarFloor s) (n : ℕ) : Paper.parisiGridMeasure μ n∈scalarFloor s := by
  rw [mem_scalarFloor_iff,parisiGridMeasure_root_mass]
  exact (mem_scalarFloor_iff s μ).mp hμ

theorem parisiFreeMeasure_grid_map (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor s) (n : ℕ) :
    (parisiFreeMeasure μ s).map (Paper.parisiGridRound n)=
      parisiFreeMeasure (Paper.parisiGridMeasure μ n) s := by
  let R : Measure Paper.Overlap:=ENNReal.ofReal s • Measure.dirac zeroOverlap
  haveI : IsFiniteMeasure R := by
    constructor
    simp only [R,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    exact ENNReal.ofReal_lt_top
  have hR : R.map (Paper.parisiGridRound n)=R := by
    dsimp only [R]
    rw [Measure.map_smul,Measure.map_dirac,parisiGridRound_zero]
    exact (Paper.measurable_parisiGridRound n).aemeasurable
  have he : R+(parisiFreeMeasure μ s).map (Paper.parisiGridRound n)=
      (Paper.parisiGridMeasure μ n : Measure Paper.Overlap) := by
    rw [←hR,←Measure.map_add _ _ (Paper.measurable_parisiGridRound n)]
    change (ENNReal.ofReal s • Measure.dirac zeroOverlap+parisiFreeMeasure μ s).map
      (Paper.parisiGridRound n)=_
    rw [root_add_parisiFreeMeasure μ s hs hμ]
    exact (ProbabilityMeasure.toMeasure_map μ).symm
  rw [parisiFreeMeasure_eq_sub _ s hs (parisiGridMeasure_mem_scalarFloor μ s hμ n),
    ←he,add_comm,Measure.add_sub_cancel]

theorem integral_parisiFreeMeasure_grid (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor s) (n : ℕ)
    (f : Paper.Overlap→ℝ) (hf : Measurable f) :
    (∫q,f q ∂parisiFreeMeasure (Paper.parisiGridMeasure μ n) s)=
      ∫q,f (Paper.parisiGridRound n q) ∂parisiFreeMeasure μ s := by
  rw [←parisiFreeMeasure_grid_map μ s hs hμ n]
  exact integral_map (Paper.measurable_parisiGridRound n).aemeasurable hf.aestronglyMeasurable

theorem parisiGridRSBScheme_root_mass (μ : Paper.ParisiMeasure) (n : ℕ) :
    (Paper.parisiGridRSBScheme μ n).m 1=zeroMass μ := by
  change Paper.parisiGridSchemeMass μ n 1=zeroMass μ
  simp only [Paper.parisiGridSchemeMass,one_ne_zero,ite_false,
    Paper.parisiGridSchemeOverlap_one]
  rw [←zeroMass_eq_parisiCDF_zero,parisiGridMeasure_root_mass]

theorem parisiGridRSBScheme_floor (μ : Paper.ParisiMeasure) (s : ℝ)
    (hμ : μ∈scalarFloor s) (n : ℕ) : s≤(Paper.parisiGridRSBScheme μ n).m 1 := by
  rw [parisiGridRSBScheme_root_mass]
  exact (mem_scalarFloor_iff s μ).mp hμ

end QuantitativeFollowup
