module
public import QuantitativeFollowup.VectorContactCriterion
public import QuantitativeFollowup.VectorTerminalOverlap
public import QuantitativeFollowup.DeficitContactGeometry

@[expose] public section

/-! Genuine contact self-consistency and upper-support exclusion for every
actual constrained vector minimizer, including contact at zero and profiles
with atoms. The strict upper bound is uniform on its compact free support. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 800000
variable {n : ℕ}

theorem vector_free_support_contact (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ico (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) :
    (q:ℝ)<1 ∧ vectorMeanOverlap (n:=n) μ β t a ht.le q=q := by
  have hcontact:=(vector_minimum_iff_free_support_argmin hn μ s ⟨hs.1,hs.2.le⟩ hs.2
    hμ β t a hβ ht ha).mp hmin hq
  have hS1 : vectorMeanOverlapReal (n:=n) μ β t a ht.le 1<1 := by
    unfold vectorMeanOverlapReal
    rw [projIcc_of_mem zero_le_one (show (1:ℝ)∈Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩)]
    exact vectorMeanOverlap_one_lt_one hn μ β t a ht.le
  have hgeometry:=transportDeficit_argmin_contact _
    (continuous_vectorMeanOverlapReal μ β t a ht.le)
    (vectorMeanOverlapReal_nonneg_le_one μ β t a ht.le 0).1 hS1 q hcontact
  refine ⟨hgeometry.1,?_⟩
  have he:=hgeometry.2
  unfold vectorMeanOverlapReal at he
  rw [projIcc_of_mem zero_le_one q.property] at he
  exact he

theorem vector_free_support_uniform_upper_bound (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ico (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a) :
    ∃Q∈Ico (0:ℝ) 1,∀q∈(parisiFreeMeasure μ s).support,(q:ℝ)≤Q := by
  have hη : parisiFreeMeasure μ s≠0 := by
    intro hz
    have hh:=parisiFreeMeasure_univ μ s
    rw [hz] at hh
    have hh' : 1-s≤0:=by simpa using hh.symm
    linarith [hs.2]
  have hc : IsCompact (parisiFreeMeasure μ s).support:=Measure.isClosed_support.isCompact
  obtain ⟨q,hq,hmax⟩:=hc.exists_isMaxOn ((parisiFreeMeasure μ s).nonempty_support hη)
    continuous_subtype_val.continuousOn
  exact ⟨q,⟨q.property.1,(vector_free_support_contact hn μ s hs hμ β t a hβ ht ha hmin q hq).1⟩,hmax⟩

theorem vector_selected_minimizer_contact (hn : 0<n) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (ha : a∈Ico (0:ℝ) 1) (q : Paper.Overlap)
    (hq : q∈(parisiFreeMeasure (vectorMeasureMinimizer n hn β t a ht.le ha.2.le) a).support) :
    (q:ℝ)<1 ∧ vectorMeanOverlap (n:=n)
      (vectorMeasureMinimizer n hn β t a ht.le ha.2.le) β t a ht.le q=q :=
  vector_free_support_contact hn _ a ha
    (vectorMeasureMinimizer_mem n hn β t a ht.le ha.2.le) β t a hβ ht ha.1
    (vectorMeasureMinimizer_minimal n hn β t a ht.le ha.2.le) q hq

end QuantitativeFollowup
