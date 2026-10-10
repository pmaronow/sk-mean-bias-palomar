module
public import QuantitativePaper.VectorFiniteControlSource
public import QuantitativePaper.VectorBoundedCellIntegral
public import FourPapersCommon.TimeIntegralTelescope

@[expose] public section

/-! Literal global control verification for each finite RSB profile.
The identity is obtained from actual cell Itô equalities, retaining empty
cells and endpoint atoms. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

theorem vectorFiniteControl_cell_identity (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (i : ℕ) (hi : i≤k+1) :
    Integrable (fun sample =>
      vectorTailRecursion s β t (s.q (i+1)) sample.1 (k+2)
        (vectorControlledState ((1-t)*β^2) μ A (s.q (i+1)).toNNReal sample)-
      vectorTailRecursion s β t (s.q i) sample.1 (k+2)
        (vectorControlledState ((1-t)*β^2) μ A (s.q i).toNNReal sample)) (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,vectorTailRecursion s β t (s.q (i+1)) sample.1 (k+2)
        (vectorControlledState ((1-t)*β^2) μ A (s.q (i+1)).toNNReal sample)-
      vectorTailRecursion s β t (s.q i) sample.1 (k+2)
        (vectorControlledState ((1-t)*β^2) μ A (s.q i).toNNReal sample) ∂vectorDisorderBrownianMeasure n)=
      ∫ sample,(∫r in Ioc (s.q i).toNNReal (s.q (i+1)).toNNReal,
        vectorFiniteControlSource s β t μ A r sample ∂nonnegativeLebesgueMeasure)
        ∂vectorDisorderBrownianMeasure n := by
  let a := (s.q i).toNNReal
  let b := (s.q (i+1)).toNNReal
  have ha : (a : ℝ)=s.q i := Real.coe_toNNReal _ (s.q_nonneg (by omega))
  have hb : (b : ℝ)=s.q (i+1) := Real.coe_toNNReal _ (s.q_nonneg (by omega))
  have hab : a≤b := Real.toNNReal_mono (s.q_mono i hi)
  have hh := vectorFiniteControlCell_ito s β t hβ ht μ A hA i hi a b hab (by rw [hb])
  have he (r : ℝ) (hr : r∈Icc (s.q i) (s.q (i+1))) (p : Couplings n×ℝ) (x : Field n) :
      vectorFiniteCellPotential s β t p i r x=vectorTailRecursion s β t r p (k+2) x :=
    congrFun (vectorTailRecursion_eq_finiteCell s β t r p i hi hr).symm x
  simp_rw [ha,hb,he _ ⟨s.q_mono i hi,le_rfl⟩,he _ ⟨le_rfl,s.q_mono i hi⟩] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply integral_congr_ae
  exact Eventually.of_forall (fun sample => by
    change (∫r in Ioc a b,vectorFiniteControlCellSource s β t μ sample.1 i r
      (vectorControlledState ((1-t)*β^2) μ A r sample) (A r sample) ∂nonnegativeLebesgueMeasure)=
        ∫r in Ioc a b,vectorFiniteControlSource s β t μ A r sample ∂nonnegativeLebesgueMeasure
    rw [integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    apply (vectorFiniteControlSource_eq_cell s β t μ A i hi r _ sample).symm
    exact ⟨by have := hr.1;change (a : ℝ)<r at this;rw [ha] at this;exact this.le,
      by have := hr.2;change (r : ℝ)<b at this;rw [hb] at this;exact this⟩)

theorem vectorFinite_control_verification (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    Integrable (fun sample => vectorTerminalPotential n β t sample.1
        (vectorControlledState ((1-t)*β^2) μ A 1 sample)-vectorRecursion s β t sample.1 (k+2) 0)
      (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,vectorTerminalPotential n β t sample.1
        (vectorControlledState ((1-t)*β^2) μ A 1 sample)-vectorRecursion s β t sample.1 (k+2) 0
      ∂vectorDisorderBrownianMeasure n)=
      ∫ sample,(∫r in Ioc 0 1,vectorFiniteControlSource s β t μ A r sample
        ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n := by
  let P := vectorDisorderBrownianMeasure n
  let a := fun i : ℕ => (s.q i).toNNReal
  let F := fun i : ℕ => fun sample : VectorDisorderBrownianSample n =>
    vectorTailRecursion s β t (s.q i) sample.1 (k+2)
      (vectorControlledState ((1-t)*β^2) μ A (a i) sample)
  let w := vectorFiniteControlSource s β t μ A
  let K : ℝ≥0 := (3*|((1-t)*β^2)| *(n : ℝ)).toNNReal
  have hK : (K : ℝ)=3*|((1-t)*β^2)| *(n : ℝ) := Real.coe_toNNReal _ (by positivity)
  have hw := measurable_vectorFiniteControlSource s β t μ A hA
  have hb (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : ‖w r sample‖≤K := by
    rw [hK]
    exact norm_vectorFiniteControlSource_le s β t μ A hA r sample
  have hwi (i : ℕ) : Integrable (fun sample => ∫r in Ioc (a i) (a (i+1)),w r sample
      ∂nonnegativeLebesgueMeasure) P := integrable_vectorBoundedCellIntegral w hw _ _ K hb
  have hFi (i : ℕ) (hi : i∈Finset.range (k+2)) : Integrable (F (i+1)-F i) P :=
    (vectorFiniteControl_cell_identity s β t hβ ht μ A hA i (by have := Finset.mem_range.mp hi;omega)).1
  have htel := Finset.sum_range_sub F (k+2)
  have htel' : (fun sample=>∑i∈Finset.range (k+2),(F (i+1)-F i) sample)=F (k+2)-F 0 := by
    funext sample
    simpa only [Finset.sum_apply] using congrFun htel sample
  have hsumI := integrable_finsetSum (Finset.range (k+2)) hFi
  rw [htel'] at hsumI
  have hFN : F (k+2)=fun sample => vectorTerminalPotential n β t sample.1
      (vectorControlledState ((1-t)*β^2) μ A 1 sample) := by
    funext sample
    simp only [F,a,s.q_top,Real.toNNReal_one]
    rw [vectorTailRecursion_one s β t sample.1 le_rfl]
  have hF0 : F 0=fun sample => vectorRecursion s β t sample.1 (k+2) 0 := by
    funext sample
    simp only [F,a,s.q_zero,Real.toNNReal_zero,vectorControlledState_zero]
    rw [vectorTailRecursion_prefix_of_le s β t 0 sample.1 le_rfl (by simp only [Nat.sub_self,s.q_zero];rfl)]
  rw [hFN,hF0] at hsumI
  refine ⟨hsumI,?_⟩
  have hsum := integral_finsetSum (Finset.range (k+2)) hFi
  rw [htel',hFN,hF0] at hsum
  refine hsum.trans ?_
  have hcell : (∑i∈Finset.range (k+2),∫sample,(F (i+1)-F i) sample ∂P)=
      ∑i∈Finset.range (k+2),∫sample,(∫r in Ioc (a i) (a (i+1)),w r sample
        ∂nonnegativeLebesgueMeasure) ∂P := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (vectorFiniteControl_cell_identity s β t hβ ht μ A hA i (by have := Finset.mem_range.mp hi;omega)).2
  rw [hcell,←integral_finsetSum _ (fun i _=>hwi i)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun sample => by
    have hi (i : ℕ) (_ : i≤k+2) : IntegrableOn (fun r=>w r sample) (Ioc (a 0) (a i))
        nonnegativeLebesgueMeasure := by
      apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top _ _) (C := (K : ℝ))).mono'
        hw.of_uncurry_right.aestronglyMeasurable
      exact Eventually.of_forall (fun r=>hb r sample)
    have hh := sum_setIntegral_Ioc_adjacent (fun r=>w r sample) nonnegativeLebesgueMeasure a (k+2)
      (fun i _=>by simp only [a,s.q_zero,Real.toNNReal_zero];exact zero_le)
      (fun i hi=>Real.toNNReal_mono (s.q_mono i (by omega))) hi
    simpa only [a,s.q_zero,s.q_top,Real.toNNReal_zero,Real.toNNReal_one] using hh)

end QuantitativePaper
