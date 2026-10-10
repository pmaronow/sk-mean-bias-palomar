module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeHistory
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeSquare

@[expose] public section

/-! Exact expectation transport from recorded posterior coordinates to the
actual restarted Wiener state. The terminal Gibbs draw is retained during the
law comparison and integrated out only for spin-independent observations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem integral_cascadePosteriorGaussianLaw_history {S : Type*}
    [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ)
    (H : FiniteStateField S) (f : FiniteHistory (FiniteStateField S) N→ℝ)
    (hf : Measurable f) (B : ℝ) (hb : ∀h,|f h|≤B) :
    (∫z,f (cascadePosteriorHistory L N H z.1)∂cascadePosteriorGaussianLaw V a L N H)=
      ∫h,f h∂cascadePosteriorHistoryLaw V a L N H := by
  haveI := cascadePosteriorHistoryLaw_probability V a ha L N H
  haveI := cascadePosteriorLaw_probability V a ha L N H
  have hi : Integrable (fun z : FiniteHistory (FiniteStateField S) N×S=>f z.1)
      (cascadePosteriorLaw V a L N H) :=
    Integrable.of_bound (hf.comp measurable_fst).aestronglyMeasurable B (.of_forall fun z=>hb z.1)
  have he := integral_map (μ:=cascadePosteriorGaussianLaw V a L N H)
    (f:=fun z : FiniteHistory (FiniteStateField S) N×S=>f z.1)
    (measurable_cascadePosteriorCoordinateMap L N H).aemeasurable
    (hf.comp measurable_fst).aestronglyMeasurable
  rw [cascadePosteriorGaussianLaw_map V a ha L N H,cascadePosteriorLaw,
    Measure.integral_compProd hi] at he
  simpa only [cascadePosteriorCoordinateMap,integral_const,probReal_univ,one_smul] using he.symm

theorem integral_anisotropicFiniteRestart_energyHistory (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (f : FiniteHistory (FiniteStateField (Configuration n)) (k+2)→ℝ)
    (hf : Measurable f) (B : ℝ) (hb : ∀h,|f h|≤B) :
    (∫z,f (cascadePosteriorHistory
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
      (k+2) (anisotropicEnergyMap D (anisotropicDisorderInjection n g+anisotropicUnitInput D x)) z.1)
      ∂cascadePosteriorGaussianLaw (fun _ : Configuration n=>0)
        (anisotropicSchemeMass (vectorClampedScheme s q q.property))
        (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
        (k+2) (anisotropicEnergyMap D (anisotropicDisorderInjection n g+anisotropicUnitInput D x)))=
      ∫sample,f (anisotropicFiniteRestartEnergyHistory D s g q x sample)
        ∂vectorDisorderBrownianMeasure n := by
  rw [integral_cascadePosteriorGaussianLaw_history _ _
    (anisotropicSchemeMass_nonneg _) _ _ _ f hf B hb,
    ←anisotropicFiniteRestartEnergyHistory_law D s g q x,
    integral_map (measurable_anisotropicFiniteRestartEnergyHistory D s g q x).aemeasurable
      hf.aestronglyMeasurable]

theorem integral_anisotropicFiniteRestart_retained_square (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (i : ℕ) (K : FiniteStateField (Configuration n)) :
    (∫z,cascadePosteriorRetainedSquare (fun _ : Configuration n=>0)
      (anisotropicSchemeMass (vectorClampedScheme s q q.property))
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
      (k+2) i K (anisotropicEnergyMap D (anisotropicDisorderInjection n g+anisotropicUnitInput D x)) z
      ∂cascadePosteriorGaussianLaw (fun _ : Configuration n=>0)
        (anisotropicSchemeMass (vectorClampedScheme s q q.property))
        (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
        (k+2) (anisotropicEnergyMap D (anisotropicDisorderInjection n g+anisotropicUnitInput D x)))=
      ∫sample,(fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
        (anisotropicSchemeMass (vectorClampedScheme s q q.property))
        (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
        (k+2-i)) (historyExtended (anisotropicFiniteRestartEnergyHistory D s g q x sample) i) K)^2
        ∂vectorDisorderBrownianMeasure n := by
  let cs:=vectorClampedScheme s q q.property
  let L:=fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D cs l)
  let f:=fun h : FiniteHistory (FiniteStateField (Configuration n)) (k+2)=>
    (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass cs) L (k+2-i)) (historyExtended h i) K)^2
  have hf : Measurable f := by
    exact ((((contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass cs) (anisotropicSchemeMass_nonneg cs) L (k+2-i)).fderiv_right
        (m:=∞) (by simp)).continuous.comp (continuous_apply (Fin.ofNat (k+3) i))).clm_apply
          continuous_const).measurable.pow_const 2
  have hb (h) : |f h|≤‖K‖^2 := by
    have hD:=finiteStateCascadeFirst_abs_le (fun _ : Configuration n=>0)
      (anisotropicSchemeMass cs) (anisotropicSchemeMass_nonneg cs) L (k+2-i) (historyExtended h i) K
    simpa only [f,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hD 2
  exact integral_anisotropicFiniteRestart_energyHistory D s g q x f hf (‖K‖^2) hb

end QuantitativeFollowup
