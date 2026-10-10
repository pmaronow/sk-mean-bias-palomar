module
public import FRSB.ParisiMinimizer
public import QuantitativePaper.Completion
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

/-! The exact scalar Parisi functional and its atom-at-zero constrained
variational problem. The closed constraint and compact attainment are proved
for the actual probability measures and the constructed PDE functional. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace QuantitativePaper
open Paper

abbrev ParisiMeasure := Paper.ParisiMeasure
abbrev Overlap := Paper.Overlap

def zeroOverlap : Overlap := ⟨0, by norm_num⟩
def zeroMass (μ : ParisiMeasure) : ℝ := (μ : Measure Overlap) {zeroOverlap} |>.toReal

def scalarParisiFunctional (β : ℝ) (μ : ParisiMeasure) : ℝ :=
  parisiPDEFunctional β 0 μ

def scalarFloor (s : ℝ) : Set ParisiMeasure :=
  {μ | ENNReal.ofReal s ≤ (μ : Measure Overlap) {zeroOverlap}}

theorem mem_scalarFloor_iff (s : ℝ) (μ : ParisiMeasure) :
    μ ∈ scalarFloor s ↔ s ≤ zeroMass μ :=
  ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)

def constrainedParisiValue (β s : ℝ) : ℝ :=
  sInf (scalarParisiFunctional β '' scalarFloor s)

@[simp] theorem scalarFloor_zero : scalarFloor 0 = univ := by
  ext μ
  simp [scalarFloor]

theorem scalarFloor_antitone {s t : ℝ} (hst : s ≤ t) : scalarFloor t ⊆ scalarFloor s :=
  fun _ hμ => (ENNReal.ofReal_le_ofReal hst).trans hμ

theorem isClosed_scalarFloor (s : ℝ) : IsClosed (scalarFloor s) := by
  apply isClosed_of_closure_subset
  intro μ hμ
  have : NeBot (𝓝[scalarFloor s] μ) := mem_closure_iff_nhdsWithin_neBot.mp hμ
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    (show Tendsto (fun ν : ParisiMeasure => ν) (𝓝[scalarFloor s] μ) (𝓝 μ) from
      tendsto_id.mono_left nhdsWithin_le_nhds)
    (isClosed_singleton : IsClosed ({zeroOverlap} : Set Overlap))
  apply le_trans _ hlim
  have hmem : ∀ᶠ ν in 𝓝[scalarFloor s] μ, ν ∈ scalarFloor s := self_mem_nhdsWithin
  exact le_limsup_of_frequently_le hmem.frequently (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)

theorem isCompact_scalarFloor (s : ℝ) : IsCompact (scalarFloor s) :=
  (isClosed_scalarFloor s).isCompact

theorem dirac_zero_mem_scalarFloor (s : ℝ) (hs : s ≤ 1) :
    diracOverlap 0 (by norm_num) ∈ scalarFloor s := by
  have hz : (diracOverlap 0 (by norm_num) : Measure Overlap) {zeroOverlap} = 1 := by
    simp [diracOverlap, zeroOverlap]
  change ENNReal.ofReal s ≤ _
  rw [hz]
  exact (ENNReal.ofReal_le_ofReal hs).trans_eq (by norm_num)

theorem scalarFloor_nonempty (s : ℝ) (hs : s ≤ 1) : (scalarFloor s).Nonempty :=
  ⟨diracOverlap 0 (by norm_num), dirac_zero_mem_scalarFloor s hs⟩

theorem continuous_scalarParisiFunctional (β : ℝ) : Continuous (scalarParisiFunctional β) :=
  FRSB.continuous_parisiPDEFunctional β 0

theorem exists_constrainedParisi_minimizer (β s : ℝ) (hs : s ≤ 1) :
    ∃ μ ∈ scalarFloor s, ∀ ν ∈ scalarFloor s,
      scalarParisiFunctional β μ ≤ scalarParisiFunctional β ν :=
  (isCompact_scalarFloor s).exists_isMinOn (scalarFloor_nonempty s hs)
    (continuous_scalarParisiFunctional β).continuousOn

/-- This selection chooses a proven actual constrained minimizer. -/
def constrainedParisiMinimizer (β s : ℝ) (hs : s ≤ 1) : ParisiMeasure :=
  Classical.choose (exists_constrainedParisi_minimizer β s hs)

theorem constrainedParisiMinimizer_mem (β s : ℝ) (hs : s ≤ 1) :
    constrainedParisiMinimizer β s hs ∈ scalarFloor s :=
  (Classical.choose_spec (exists_constrainedParisi_minimizer β s hs)).1

theorem constrainedParisiMinimizer_minimal (β s : ℝ) (hs : s ≤ 1)
    (ν : ParisiMeasure) (hν : ν ∈ scalarFloor s) :
    scalarParisiFunctional β (constrainedParisiMinimizer β s hs) ≤ scalarParisiFunctional β ν :=
  (Classical.choose_spec (exists_constrainedParisi_minimizer β s hs)).2 ν hν

theorem constrainedParisiValue_eq_minimum (β s : ℝ) (hs : s ≤ 1) :
    constrainedParisiValue β s = scalarParisiFunctional β (constrainedParisiMinimizer β s hs) := by
  have hb : BddBelow (scalarParisiFunctional β '' scalarFloor s) := by
    refine ⟨scalarParisiFunctional β (constrainedParisiMinimizer β s hs), ?_⟩
    rintro r ⟨μ,hμ,rfl⟩
    exact constrainedParisiMinimizer_minimal β s hs μ hμ
  unfold constrainedParisiValue
  apply le_antisymm
  · exact csInf_le hb ⟨_,constrainedParisiMinimizer_mem β s hs,rfl⟩
  · apply le_csInf ((scalarFloor_nonempty s hs).image _)
    rintro r ⟨μ,hμ,rfl⟩
    exact constrainedParisiMinimizer_minimal β s hs μ hμ

theorem constrainedParisiValue_le (β s : ℝ) (hs : s ≤ 1)
    (μ : ParisiMeasure) (hμ : μ ∈ scalarFloor s) :
    constrainedParisiValue β s ≤ scalarParisiFunctional β μ := by
  rw [constrainedParisiValue_eq_minimum β s hs]
  exact constrainedParisiMinimizer_minimal β s hs μ hμ

theorem constrainedParisiValue_mono (β : ℝ) {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 1) :
    constrainedParisiValue β s ≤ constrainedParisiValue β t := by
  rw [constrainedParisiValue_eq_minimum β t ht]
  exact constrainedParisiValue_le β s (hst.trans ht) _
    (scalarFloor_antitone hst (constrainedParisiMinimizer_mem β t ht))

@[simp] theorem constrainedParisiValue_zero (β : ℝ) :
    constrainedParisiValue β 0 = parisiPDEValue β 0 := by
  unfold constrainedParisiValue
  rw [scalarFloor_zero]
  congr 1
  ext r
  simp [scalarParisiFunctional, eq_comm]

end QuantitativePaper
