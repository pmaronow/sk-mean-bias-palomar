module
public import QuantitativeFollowup.ParisiFreeMeasure
public import FourPapersCommon.ProbabilityIntegralContinuity

@[expose] public section

/-! Integration against the actual free overlap measure is jointly
continuous under weak changes of a profile with fixed prescribed root mass.
The removed root atom is accounted for exactly, including extra mass at zero. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FourPapersCommon
open scoped Topology ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem integral_parisiFreeMeasure_continuous (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor s) (f : Paper.Overlap → ℝ) (hf : Continuous f) :
    (∫ q,f q ∂parisiFreeMeasure μ s)=(∫ q,f q ∂(μ : Measure Paper.Overlap))-s*f zeroOverlap := by
  have hiν : Integrable f (parisiFreeMeasure μ s) := by
    simpa only [IntegrableOn,Measure.restrict_univ] using hf.continuousOn.integrableOn_compact
      (μ := parisiFreeMeasure μ s) isCompact_univ
  have hi₀ : Integrable f (ENNReal.ofReal s • Measure.dirac zeroOverlap) :=
    (integrable_dirac (a := zeroOverlap) (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  have he := integral_add_measure hi₀ hiν
  rw [root_add_parisiFreeMeasure μ s hs hμ] at he
  simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal hs.1,smul_eq_mul] at he
  linarith

theorem continuous_integral_parisiFreeMeasure_family {A : Type*} [TopologicalSpace A]
    (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) (μ : A → Paper.ParisiMeasure)
    (hμ : Continuous μ) (hfloor : ∀ a,μ a∈scalarFloor s)
    (f : A×Paper.Overlap → ℝ) (hf : Continuous f) :
    Continuous (fun a => ∫ q,f (a,q) ∂parisiFreeMeasure (μ a) s) := by
  have hprob := continuous_integral_probability_family f hf μ hμ
  have hroot : Continuous (fun a : A => f (a,zeroOverlap)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have he : (fun a => ∫ q,f (a,q) ∂parisiFreeMeasure (μ a) s)=
      (fun a => (∫ q,f (a,q) ∂(μ a : Measure Paper.Overlap))-s*f (a,zeroOverlap)) := by
    funext a
    exact integral_parisiFreeMeasure_continuous (μ a) s hs (hfloor a) _
      (hf.comp (continuous_const.prodMk continuous_id))
  rw [he]
  exact hprob.sub (continuous_const.mul hroot)

end QuantitativeFollowup
