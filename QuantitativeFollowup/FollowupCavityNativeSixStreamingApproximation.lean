module
public import FRSB.FiniteSchemeRepresentation
public import QuantitativeFollowup.ParisiFreeGrid

@[expose] public section

/-! Finite approximations for the native streaming formula retain every
prescribed branch atom and right CDF exactly.  Their free measures are
actual pushforwards of the original free measure. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128

theorem nativeStreaming_preserving_root_mass (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap ∈ S) (N : ℕ) :
    zeroMass (FRSB.preservingMeasure μ S N)=zeroMass μ := by
  rw [zeroMass_eq_parisiCDF_zero,zeroMass_eq_parisiCDF_zero]
  exact FRSB.preservingMeasure_cdf_mass μ S N zeroOverlap hzero

theorem nativeStreaming_preserving_floor (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap ∈ S)
    (a : ℝ) (hμ : μ∈scalarFloor a) (N : ℕ) :
    FRSB.preservingMeasure μ S N∈scalarFloor a := by
  rw [mem_scalarFloor_iff,nativeStreaming_preserving_root_mass μ S hzero]
  exact (mem_scalarFloor_iff a μ).mp hμ

theorem nativeStreaming_free_preserving_map (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap ∈ S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (N : ℕ) :
    (parisiFreeMeasure μ a).map (FRSB.preservingRound S N)=
      parisiFreeMeasure (FRSB.preservingMeasure μ S N) a := by
  let R : Measure Paper.Overlap:=ENNReal.ofReal a • Measure.dirac zeroOverlap
  haveI : IsFiniteMeasure R := by
    constructor
    simp only [R,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    exact ENNReal.ofReal_lt_top
  have hR : R.map (FRSB.preservingRound S N)=R := by
    dsimp only [R]
    rw [Measure.map_smul,Measure.map_dirac,FRSB.preservingRound_fixed S N zeroOverlap hzero]
    exact (FRSB.measurable_preservingRound S N).aemeasurable
  have he : R+(parisiFreeMeasure μ a).map (FRSB.preservingRound S N)=
      (FRSB.preservingMeasure μ S N : Measure Paper.Overlap) := by
    rw [←hR,←Measure.map_add _ _ (FRSB.measurable_preservingRound S N)]
    change (ENNReal.ofReal a • Measure.dirac zeroOverlap+parisiFreeMeasure μ a).map
      (FRSB.preservingRound S N)=_
    rw [root_add_parisiFreeMeasure μ a ha hμ]
    exact (ProbabilityMeasure.toMeasure_map μ).symm
  rw [parisiFreeMeasure_eq_sub _ a ha
    (nativeStreaming_preserving_floor μ S hzero a hμ N),
    ←he,add_comm,Measure.add_sub_cancel]

theorem nativeStreaming_free_atom_preserved (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap ∈ S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (N : ℕ)
    (q : Paper.Overlap) (hq : q∈S) :
    parisiFreeMeasure (FRSB.preservingMeasure μ S N) a {q}=parisiFreeMeasure μ a {q} := by
  rw [←nativeStreaming_free_preserving_map μ S hzero a ha hμ N,
    Measure.map_apply (FRSB.measurable_preservingRound S N) (measurableSet_singleton q)]
  congr 1
  ext r
  exact FRSB.preservingRound_eq_iff S N r q hq

/-- The literal charge of a branch with `l` children; the atom belongs to
the genuine free Stieltjes measure, including the subtracted root atom. -/
def nativeStreamingBranchCharge (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : Paper.Overlap) (l : ℕ) : ℝ :=
  (parisiFreeMeasure μ a).real {q}+(l-1:ℝ)*Paper.parisiCDF μ q

theorem nativeStreaming_branch_charge_preserved (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap ∈ S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (N : ℕ)
    (q : Paper.Overlap) (hq : q∈S) (l : ℕ) :
    nativeStreamingBranchCharge (FRSB.preservingMeasure μ S N) a q l=
      nativeStreamingBranchCharge μ a q l := by
  unfold nativeStreamingBranchCharge Measure.real
  rw [nativeStreaming_free_atom_preserved μ S hzero a ha hμ N q hq,
    FRSB.preservingMeasure_cdf_mass μ S N q hq]

theorem nativeStreaming_integral_free_preserving (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap ∈ S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (N : ℕ)
    (f : Paper.Overlap→ℝ) (hf : Measurable f) :
    (∫q,f q ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a)=
      ∫q,f (FRSB.preservingRound S N q) ∂parisiFreeMeasure μ a := by
  rw [←nativeStreaming_free_preserving_map μ S hzero a ha hμ N]
  exact integral_map (FRSB.measurable_preservingRound S N).aemeasurable hf.aestronglyMeasurable

theorem nativeStreaming_round_mem_prescribed_iff (S : Finset Paper.Overlap)
    (N : ℕ) (r : Paper.Overlap) :
    FRSB.preservingRound S N r∈S ↔ r∈S := by
  constructor
  · intro hr
    have he:FRSB.preservingRound S N r=r:=
      ((FRSB.preservingRound_eq_iff S N r (FRSB.preservingRound S N r) hr).mp rfl).symm
    simpa only [he] using hr
  · intro hr
    rw [FRSB.preservingRound_fixed S N r hr]
    exact hr

theorem nativeStreaming_integral_strict_future_preserving (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap ∈ S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (N : ℕ)
    (q : Paper.Overlap) (hq : q∈S) (f : Paper.Overlap→ℝ) (hf : Measurable f) :
    (∫r,if q<r then f r else 0 ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a)=
      ∫r,if q<r then f (FRSB.preservingRound S N r) else 0 ∂parisiFreeMeasure μ a := by
  rw [nativeStreaming_integral_free_preserving μ S hzero a ha hμ N
    (fun r=>if q<r then f r else 0)
    (Measurable.ite isOpen_Ioi.measurableSet hf measurable_const)]
  apply integral_congr_ae
  exact .of_forall fun r=>by
    dsimp only
    simp only [FRSB.preservingRound_gt_iff S N r q hq]

/-- The open edge excludes all prescribed branch levels before and after
rounding.  Atoms are retained by this exact equality. -/
theorem nativeStreaming_integral_edge_preserving (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap ∈ S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (N : ℕ)
    (b c : Paper.Overlap) (hb : b∈S) (hc : c∈S)
    (f : Paper.Overlap→ℝ) (hf : Measurable f) :
    (∫r,if b<r ∧ r<c ∧ r∉S then f r else 0
      ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a)=
      ∫r,if b<r ∧ r<c ∧ r∉S then f (FRSB.preservingRound S N r) else 0
        ∂parisiFreeMeasure μ a := by
  have hset:MeasurableSet {r:Paper.Overlap | b<r ∧ r<c ∧ r∉S}:=
    isOpen_Ioi.measurableSet.inter (isOpen_Iio.measurableSet.inter S.finite_toSet.measurableSet.compl)
  rw [nativeStreaming_integral_free_preserving μ S hzero a ha hμ N
    (fun r=>if b<r ∧ r<c ∧ r∉S then f r else 0)
    (Measurable.ite hset hf measurable_const)]
  apply integral_congr_ae
  exact .of_forall fun r=>by
    dsimp only
    simp only [FRSB.preservingRound_gt_iff S N r b hb,
      FRSB.preservingRound_lt_iff S N r c hc,nativeStreaming_round_mem_prescribed_iff]

end QuantitativeFollowup
