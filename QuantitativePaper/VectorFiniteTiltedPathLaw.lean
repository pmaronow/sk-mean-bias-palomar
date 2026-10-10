module
public import QuantitativePaper.VectorFinitePathLaw

@[expose] public section

/-! Exact fractional initial-disorder density transport for the constructed
finite vector diffusion. Unbounded normalized exponential weights are
handled by measure transport, without bounded-weight approximation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

theorem measurable_vectorOuterWeight (s : RSBScheme k) (β t a : ℝ) :
    Measurable (vectorOuterWeight (n:=n) s β t a) := by
  unfold vectorOuterWeight
  exact ((Real.measurable_exp.comp (measurable_const.mul
    ((measurable_vectorRecursion s β t (k+2)).comp
      (measurable_id.prodMk measurable_const)))).div_const _)

theorem vectorInitialLaw_withDensity_zero (s : RSBScheme k) (β t a : ℝ) :
    vectorInitialLaw (n:=n) s β t a=
      (vectorInitialLaw s β t 0).withDensity
        (fun x=>ENNReal.ofReal (vectorOuterWeight s β t a x.1)) := by
  rw [vectorInitialLaw,vectorInitialLaw,vectorOuterLaw_zero]
  exact map_withDensity_pullback (completionLaw n) (fun p=>(p,0))
    (measurable_id.prodMk measurable_const)
    (fun x : VectorState n=>ENNReal.ofReal (vectorOuterWeight s β t a x.1))
    (((measurable_vectorOuterWeight s β t a).comp measurable_fst).ennreal_ofReal)

def vectorFiniteDisorderTilt (s : RSBScheme k) (β t a : ℝ) :
    Measure (VectorDisorderBrownianSample n) :=
  (vectorDisorderBrownianMeasure n).withDensity
    (fun sample=>ENNReal.ofReal (vectorOuterWeight s β t a sample.1))

theorem vectorFinite_tilted_full_history_law (s : RSBScheme k) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) :
    (vectorFiniteDisorderTilt s β t a).map
      (vectorFiniteHistory s β t ht.le (k+2))=vectorFieldHistoryLaw (n:=n) s β t a := by
  let w : VectorState n→ℝ≥0∞ := fun x=>ENNReal.ofReal (vectorOuterWeight s β t a x.1)
  have hw : Measurable w :=
    (((measurable_vectorOuterWeight s β t a).comp measurable_fst).ennreal_ofReal)
  have hwt : ∀ sample : VectorDisorderBrownianSample n,
      w ((vectorFiniteHistory s β t ht.le (k+2) sample) 0)=
        ENNReal.ofReal (vectorOuterWeight s β t a sample.1) := fun _=>rfl
  have he := map_withDensity_pullback (vectorDisorderBrownianMeasure n)
    (vectorFiniteHistory s β t ht.le (k+2))
    (measurable_vectorFiniteHistory s β t ht.le (k+2))
    (fun p : FiniteHistory (VectorState n) (k+2)=>w (p 0))
    (hw.comp (measurable_pi_apply 0))
  simp only [hwt,vectorFinite_full_history_law s β t hβ ht] at he
  rw [show (vectorFiniteDisorderTilt s β t a).map
      (vectorFiniteHistory s β t ht.le (k+2))=
      (vectorFieldHistoryLaw (n:=n) s β t 0).withDensity
        (fun p=>w (p 0)) from he]
  letI := vectorOuterLaw_probability (n:=n) s β t 0
  letI := vectorOuterLaw_probability (n:=n) s β t a
  letI : IsProbabilityMeasure (vectorInitialLaw (n:=n) s β t 0) := by
    unfold vectorInitialLaw
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  letI : IsProbabilityMeasure (vectorInitialLaw (n:=n) s β t a) := by
    unfold vectorInitialLaw
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  exact (finiteHistoryLaw_withDensity_initial (vectorInitialLaw s β t 0)
    (vectorInitialLaw s β t a) (vectorProfileKernel s β t) (vectorProfileKernel_markov s β t)
    w hw (vectorInitialLaw_withDensity_zero s β t a) (k+2)).symm

theorem vectorFiniteDisorderTilt_probability (s : RSBScheme k) (β t a : ℝ) :
    IsProbabilityMeasure (vectorFiniteDisorderTilt (n:=n) s β t a) := by
  constructor
  rw [vectorFiniteDisorderTilt,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [←lintegral_map (measurable_vectorOuterWeight s β t a).ennreal_ofReal measurable_fst,
    (hasLaw_initialVectorDisorder n).map_eq]
  haveI := vectorOuterLaw_probability (n:=n) s β t a
  have h := measure_univ (μ:=vectorOuterLaw (n:=n) s β t a)
  rw [vectorOuterLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at h
  exact h

end QuantitativePaper
