module
public import QuantitativeFollowup.AnisotropicFiniteFixedHistoryLaw
public import QuantitativeFollowup.AnisotropicFiniteParameterMeasurable

@[expose] public section

/-! Mixing the true fixed-disorder diffusion histories against the genuine
 anisotropic tilted disorder gives exactly the literal finite-profile
 history law. The auxiliary independent Gaussian coordinate is harmless
 and retained explicitly in this common Wiener realization. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal ENNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

abbrev AnisotropicFiniteDiffusionSample (n : ℕ) := AnisotropicDisorder n×VectorDisorderBrownianSample n

def anisotropicFiniteDiffusionSampleLaw (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) :
    Measure (AnisotropicFiniteDiffusionSample n) :=
  (anisotropicFiniteOuterLaw D s a).prod (vectorDisorderBrownianMeasure n)

instance anisotropicFiniteDiffusionSampleLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : IsProbabilityMeasure (anisotropicFiniteDiffusionSampleLaw D s a) := by
  unfold anisotropicFiniteDiffusionSampleLaw
  infer_instance

def anisotropicFiniteDiffusionHistory (D : AnisotropicSpinModel n) (s : RSBScheme k) (j : ℕ)
    (sample : AnisotropicFiniteDiffusionSample n) : FiniteHistory (AnisotropicParameter n) j :=
  anisotropicFinitePhysicalHistory D s sample.1 j sample.2

theorem measurable_anisotropicFiniteDiffusionHistory (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) : Measurable (anisotropicFiniteDiffusionHistory D s j) := by
  apply Measurable.of_eval
  intro i
  change Measurable (fun z : AnisotropicFiniteDiffusionSample n=>
    anisotropicDisorderInjection n z.1+anisotropicUnitInput D
      (anisotropicWhitenedFiniteState D s z.1 (s.q i).toNNReal z.2))
  exact ((anisotropicDisorderInjection n).continuous.measurable.comp measurable_fst).add
    ((anisotropicUnitInput D).continuous.measurable.comp
      (measurable_anisotropicWhitenedFiniteState_parameter D s (s.q i).toNNReal))

def anisotropicFiniteDiffusionHistoryKernel (D : AnisotropicSpinModel n) (s : RSBScheme k) (j : ℕ) :
    Kernel (AnisotropicDisorder n) (FiniteHistory (AnisotropicParameter n) j) :=
  ((Kernel.id : Kernel (AnisotropicDisorder n) (AnisotropicDisorder n))×ₖ
    Kernel.const (AnisotropicDisorder n) (vectorDisorderBrownianMeasure n)).map
      (anisotropicFiniteDiffusionHistory D s j)

theorem anisotropicFiniteDiffusionHistoryKernel_apply (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (g : AnisotropicDisorder n) :
    anisotropicFiniteDiffusionHistoryKernel D s j g=
      (vectorDisorderBrownianMeasure n).map (anisotropicFinitePhysicalHistory D s g j) := by
  rw [anisotropicFiniteDiffusionHistoryKernel,
    Kernel.map_apply _ (measurable_anisotropicFiniteDiffusionHistory D s j),
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (measurable_anisotropicFiniteDiffusionHistory D s j) measurable_prodMk_left]
  rfl

theorem anisotropicFiniteDiffusionHistoryKernel_eq (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (hj : j ≤ k+2) :
    anisotropicFiniteDiffusionHistoryKernel D s j=
      (finiteHistoryKernel (anisotropicFiniteTransition D s) j).comap
        (anisotropicDisorderInjection n) (anisotropicDisorderInjection n).continuous.measurable := by
  ext g A hA
  rw [anisotropicFiniteDiffusionHistoryKernel_apply,Kernel.comap_apply,
    anisotropicFinitePhysicalFixed_history_kernel D s g j hj]

theorem anisotropicFiniteDiffusion_history_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (j : ℕ) (hj : j ≤ k+2) :
    (anisotropicFiniteDiffusionSampleLaw D s a).map (anisotropicFiniteDiffusionHistory D s j)=
      finiteHistoryLaw (anisotropicFiniteInitialLaw D s a) (anisotropicFiniteTransition D s) j := by
  have hinj := (anisotropicDisorderInjection n).continuous.measurable
  change ((anisotropicFiniteOuterLaw D s a).prod (vectorDisorderBrownianMeasure n)).map _=_
  rw [←Measure.compProd_const,Measure.compProd_eq_comp_prod,
    Measure.map_comp _ _ (measurable_anisotropicFiniteDiffusionHistory D s j)]
  change (anisotropicFiniteDiffusionHistoryKernel D s j)∘ₘ(anisotropicFiniteOuterLaw D s a)=_
  rw [anisotropicFiniteDiffusionHistoryKernel_eq D s j hj]
  change ((finiteHistoryKernel (anisotropicFiniteTransition D s) j).comap
    (anisotropicDisorderInjection n) hinj)∘ₘ(anisotropicFiniteOuterLaw D s a)=_
  rw [←Kernel.comp_deterministic_eq_comap _ hinj,←Measure.comp_assoc,
    Measure.deterministic_comp_eq_map hinj,finiteHistoryKernel_comp _ _ (fun _=>inferInstance)]
  rfl

theorem anisotropicFiniteDiffusion_full_history_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) :
    (anisotropicFiniteDiffusionSampleLaw D s a).map (anisotropicFiniteDiffusionHistory D s (k+2))=
      anisotropicFiniteHistoryLaw D s a :=
  anisotropicFiniteDiffusion_history_law D s a (k+2) le_rfl

end QuantitativeFollowup
