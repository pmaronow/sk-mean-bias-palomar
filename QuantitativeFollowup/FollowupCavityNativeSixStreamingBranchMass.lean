module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingApproximation

@[expose] public section

/-! The exact branch coefficient is outgoing right mass minus incoming
left mass. The prescribed root mass is removed at zero, so the resulting
atom is the genuine free atom in the printed branch weight. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 700000

theorem nativeStreaming_cdf_left_atom (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Paper.parisiCDF μ q=(μ:Measure Paper.Overlap).real (Iio q)+(μ:Measure Paper.Overlap).real {q} := by
  change (μ:Measure Paper.Overlap).real (Iic q)=_
  rw [←Iio_union_right]
  apply measureReal_union
  · exact disjoint_left.mpr fun r hr hsq=>by
      have he:r=q:=mem_singleton_iff.mp hsq
      exact (ne_of_lt hr) (congrArg Subtype.val he)
  · exact measurableSet_singleton _
  · exact measure_ne_top _ _
  · exact measure_ne_top _ _

theorem nativeStreaming_free_atom_root_split (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (q : Paper.Overlap) :
    (μ:Measure Paper.Overlap).real {q}=(parisiFreeMeasure μ a).real {q}+
      (if q=zeroOverlap then a else 0) := by
  haveI : IsFiniteMeasure (ENNReal.ofReal a • Measure.dirac (zeroOverlap:Paper.Overlap)) := by
    constructor
    simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    exact ENNReal.ofReal_lt_top
  rw [←root_add_parisiFreeMeasure μ a ha hμ,Measure.real,Measure.add_apply,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),Measure.smul_apply,
    smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal ha.1]
  by_cases he:q=zeroOverlap
  · subst q
    simp only [Measure.dirac_apply_of_mem (mem_singleton _),ENNReal.toReal_one,mul_one,ite_true]
    exact add_comm _ _
  · rw [Measure.dirac_apply' _ (measurableSet_singleton _),
      Set.indicator_of_notMem (by simpa only [mem_singleton_iff,eq_comm] using he)]
    simp [he,Measure.real]

def nativeStreamingIncomingBranchMass (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : Paper.Overlap) : ℝ :=
  (μ:Measure Paper.Overlap).real (Iio q)+(if q=zeroOverlap then a else 0)

theorem nativeStreamingBranchCharge_eq_outgoing_minus_incoming
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) (q : Paper.Overlap) (l : ℕ) :
    nativeStreamingBranchCharge μ a q l=
      (l:ℝ)*Paper.parisiCDF μ q-nativeStreamingIncomingBranchMass μ a q := by
  have hc:=nativeStreaming_cdf_left_atom μ q
  have hr:=nativeStreaming_free_atom_root_split μ a ha hμ q
  unfold nativeStreamingBranchCharge nativeStreamingIncomingBranchMass
  nlinarith only [hc,hr]

theorem nativeStreamingIncomingBranchMass_preserved (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (N : ℕ) (a : ℝ) (q : Paper.Overlap) (hq : q∈S) :
    nativeStreamingIncomingBranchMass (FRSB.preservingMeasure μ S N) a q=
      nativeStreamingIncomingBranchMass μ a q := by
  unfold nativeStreamingIncomingBranchMass Measure.real
  rw [FRSB.preservingMeasure_left_mass μ S N q hq]

end QuantitativeFollowup
