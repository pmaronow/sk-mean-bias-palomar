module
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.AEMeasurable

@[expose] public section

/-! A finite chart decomposition uses one measure. Null overlaps and an
almost-everywhere cover are enough, and a common measurable pushforward
preserves the exact decomposition. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators
namespace FourPapersCommon
variable {ι H G : Type*} [Fintype ι] [MeasurableSpace H] [MeasurableSpace G]
set_option autoImplicit false

theorem finiteMeasureChartPartition_sum_restrict_ae
    (M : Measure H) (E : ι → Set H)
    (hE : ∀ i, NullMeasurableSet (E i) M)
    (hd : Pairwise (AEDisjoint M on E))
    (hcover : ∀ᵐ x ∂M, ∃ i, x ∈ E i) :
    (∑ i, M.restrict (E i)) = M := by
  classical
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion_ae hd hE]
  apply Measure.restrict_eq_self_of_ae_mem
  simpa only [Set.mem_iUnion] using hcover

theorem finiteMeasureChartPartition_sum_restrict
    (M : Measure H) (E : ι → Set H)
    (hE : ∀ i, MeasurableSet (E i))
    (hd : Pairwise (Disjoint on E))
    (hcover : ∀ᵐ x ∂M, ∃ i, x ∈ E i) :
    (∑ i, M.restrict (E i)) = M :=
  finiteMeasureChartPartition_sum_restrict_ae M E
    (fun i => (hE i).nullMeasurableSet) hd.aedisjoint hcover

theorem finiteMeasureChartPartition_sum_map_restrict_ae
    (M : Measure H) (E : ι → Set H)
    (hE : ∀ i, NullMeasurableSet (E i) M)
    (hd : Pairwise (AEDisjoint M on E))
    (hcover : ∀ᵐ x ∂M, ∃ i, x ∈ E i)
    (g : H → G) (hg : Measurable g) :
    (∑ i, (M.restrict (E i)).map g) = M.map g := by
  classical
  rw [← Measure.map_finset_sum' hg.aemeasurable,
    finiteMeasureChartPartition_sum_restrict_ae M E hE hd hcover]

theorem finiteMeasureChartPartition_sum_map_restrict
    (M : Measure H) (E : ι → Set H)
    (hE : ∀ i, MeasurableSet (E i))
    (hd : Pairwise (Disjoint on E))
    (hcover : ∀ᵐ x ∂M, ∃ i, x ∈ E i)
    (g : H → G) (hg : Measurable g) :
    (∑ i, (M.restrict (E i)).map g) = M.map g :=
  finiteMeasureChartPartition_sum_map_restrict_ae M E
    (fun i => (hE i).nullMeasurableSet) hd.aedisjoint hcover g hg

end FourPapersCommon
