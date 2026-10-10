module
public import QuantitativePaper.VectorDriftBounds
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

@[expose] public section

/-! Actual translation of restricted nonnegative Lebesgue time measure. -/
noncomputable section
open MeasureTheory Set StochasticCalculus
open scoped NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem map_nonnegativeLebesgue_restrict_Ioc_coe (a b : ℝ≥0) :
    Measure.map ((↑) : ℝ≥0→ℝ) (nonnegativeLebesgueMeasure.restrict (Ioc a b))=
      (volume : Measure ℝ).restrict (Ioc (a : ℝ) b) := by
  let f : ℝ≥0→ℝ := (↑)
  have hf : MeasurableEmbedding f := measurableEmbedding_nnrealCoe_iterated
  have hp : f ⁻¹' Ioc (a : ℝ) b=Ioc a b := by
    ext s
    simp only [mem_preimage,mem_Ioc,f]
    exact and_congr (by norm_cast) (by norm_cast)
  rw [←hp,←hf.restrict_map]
  change (Measure.map f (Measure.comap f (volume : Measure ℝ))).restrict
    (Ioc (a : ℝ) b)=_
  rw [hf.map_comap,NNReal.range_coe,Measure.restrict_restrict measurableSet_Ioc]
  congr 1
  ext s
  simp only [mem_inter_iff,mem_Ioc,mem_Ici]
  constructor
  · exact fun hs=>hs.1
  · intro hs
    exact ⟨hs,a.coe_nonneg.trans hs.1.le⟩

theorem map_nonnegativeLebesgue_restrict_Ioc_add (a t : ℝ≥0) :
    Measure.map (fun r : ℝ≥0=>a+r) (nonnegativeLebesgueMeasure.restrict (Ioc 0 t))=
      nonnegativeLebesgueMeasure.restrict (Ioc a (a+t)) := by
  apply (measurableEmbedding_nnrealCoe_iterated.map_injective)
  rw [Measure.map_map (by fun_prop) (by fun_prop),map_nonnegativeLebesgue_restrict_Ioc_coe]
  have he : ((↑) : ℝ≥0→ℝ) ∘ (fun r=>a+r)=
      (fun r : ℝ=>(a : ℝ)+r) ∘ ((↑) : ℝ≥0→ℝ) := by
    funext r
    simp only [Function.comp_apply,NNReal.coe_add]
  rw [he,←Measure.map_map (by fun_prop) (by fun_prop),
    map_nonnegativeLebesgue_restrict_Ioc_coe]
  have hp : (fun r : ℝ=>(a : ℝ)+r) ⁻¹' Ioc (a : ℝ) ((a : ℝ)+t)=Ioc 0 (t : ℝ) := by
    ext r
    simp only [mem_preimage,mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  have hf : MeasurableEmbedding (fun r : ℝ=>(a : ℝ)+r) :=
    (MeasurableEquiv.addLeft (a : ℝ)).measurableEmbedding
  simp only [NNReal.coe_zero,NNReal.coe_add]
  rw [←hp,←hf.restrict_map,(measurePreserving_add_left (volume : Measure ℝ) (a : ℝ)).map_eq]

theorem integral_nonnegativeTime_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ≥0→E) (hf : AEStronglyMeasurable f nonnegativeLebesgueMeasure)
    (a t : ℝ≥0) :
    (∫ r in Ioc 0 t,f (a+r) ∂nonnegativeLebesgueMeasure)=
      ∫ r in Ioc a (a+t),f r ∂nonnegativeLebesgueMeasure := by
  have hm : AEStronglyMeasurable f
      (Measure.map (fun r : ℝ≥0=>a+r) (nonnegativeLebesgueMeasure.restrict (Ioc 0 t))) := by
    rw [map_nonnegativeLebesgue_restrict_Ioc_add a t]
    exact hf.restrict
  rw [←map_nonnegativeLebesgue_restrict_Ioc_add a t,
    integral_map (by fun_prop : AEMeasurable (fun r : ℝ≥0=>a+r) _) hm]

theorem vectorIntegratedDrift_add {n : ℕ} (d : ℝ≥0→QuantitativePaper.Field n)
    (hd : Measurable d) (D : ℝ≥0) (hD : ∀ r,‖d r‖≤D) (a t : ℝ≥0) :
    QuantitativePaper.vectorIntegratedDrift (fun r=>d (a+r)) t=
      QuantitativePaper.vectorIntegratedDrift d (a+t)-QuantitativePaper.vectorIntegratedDrift d a := by
  rw [QuantitativePaper.vectorIntegratedDrift_sub d (le_add_of_nonneg_right t.coe_nonneg)]
  · exact integral_nonnegativeTime_add d hd.aestronglyMeasurable a t
  · exact QuantitativePaper.integrableOn_bounded_vector_drift d hd D hD 0 (a+t)

end FourPapersCommon
