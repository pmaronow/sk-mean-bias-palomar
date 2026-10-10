module
public import HexagonPaper.PrefixLikelihoodContinuity
public import FRSB.MeasureApproximation
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

@[expose] public section

/-! Exact prefix Radon--Nikodym law on the full continuous path space for
every probability overlap profile. Finite schemes are only approximants;
the conclusion contains the given profile and all of its atoms. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem isFiniteMeasure_scalarPrefixReference (β : ℝ) (μ : Paper.ParisiMeasure)
    (t : ℝ≥0) (ht : (t:ℝ)≤1) :
    IsFiniteMeasure (canonicalBrownianMeasure.withDensity (forwardBrownianWeight β μ t)) := by
  apply isFiniteMeasure_withDensity
  change (∫⁻sample,ENNReal.ofReal (scalarPrefixLikelihood β μ t sample)
    ∂canonicalBrownianMeasure)≠∞
  rw [←ofReal_integral_eq_lintegral_ofReal
    (integrable_scalarPrefixLikelihood β μ t ht)
      (.of_forall fun sample=>(Real.exp_pos _).le)]
  exact ENNReal.ofReal_ne_top

theorem integral_scalarStoppedBrownianPath_withDensity (β : ℝ) (μ : Paper.ParisiMeasure)
    (t : ℝ≥0) (ψ : C(Paper.Overlap,ℝ)→ᵇℝ) :
    (∫p,ψ p ∂(canonicalBrownianMeasure.withDensity (forwardBrownianWeight β μ t)).map
      (scalarStoppedBrownianPath β t))=
        ∫sample,scalarPrefixLikelihood β μ t sample * ψ (scalarStoppedBrownianPath β t sample)
          ∂canonicalBrownianMeasure := by
  rw [integral_map_of_stronglyMeasurable (measurable_scalarStoppedBrownianPath β t)
    ψ.continuous.measurable.stronglyMeasurable]
  change (∫sample,ψ (scalarStoppedBrownianPath β t sample)
    ∂canonicalBrownianMeasure.withDensity (fun sample=>ENNReal.ofReal
      (scalarPrefixLikelihood β μ t sample)))=_
  rw [integral_withDensity_eq_integral_toReal_smul
    (by change Measurable (fun sample=>ENNReal.ofReal (scalarPrefixLikelihood β μ t sample))
        exact (measurable_scalarPrefixLikelihood β μ t).ennreal_ofReal)
      (.of_forall fun _=>ENNReal.ofReal_lt_top)]
  simp only [scalarPrefixLikelihood,ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]

theorem tendsto_integral_scalarStoppedStatePath_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (ν : A→Paper.ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (t : ℝ≥0) (ht : (t:ℝ)≤1)
    (ψ : C(Paper.Overlap,ℝ)→ᵇℝ) :
    Tendsto (fun i=>∫sample,ψ (scalarStoppedStatePath β (ν i) t sample)
      ∂canonicalBrownianMeasure) l
        (𝓝 (∫sample,ψ (scalarStoppedStatePath β μ t sample) ∂canonicalBrownianMeasure)) := by
  apply tendsto_integral_filter_of_dominated_convergence (bound:=fun _=>‖ψ‖)
  · exact .of_forall fun i=>(ψ.continuous.measurable.comp
      (measurable_scalarStoppedStatePath β hβ (ν i) t ht)).aestronglyMeasurable
  · exact .of_forall fun _=>.of_forall fun sample=>ψ.norm_coe_le_norm _
  · exact integrable_const _
  · exact .of_forall fun sample=>ψ.continuous.continuousAt.tendsto.comp
      (tendsto_scalarStoppedStatePath_of_weak β μ ν hν t ht sample)

theorem tendsto_integral_scalarPrefixObservable_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (μ : Paper.ParisiMeasure) (ν : A→Paper.ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) (t : ℝ≥0) (ht : (t:ℝ)≤1)
    (ψ : C(Paper.Overlap,ℝ)→ᵇℝ) :
    Tendsto (fun i=>∫sample,scalarPrefixLikelihood β (ν i) t sample *
      ψ (scalarStoppedBrownianPath β t sample) ∂canonicalBrownianMeasure) l
        (𝓝 (∫sample,scalarPrefixLikelihood β μ t sample *
          ψ (scalarStoppedBrownianPath β t sample) ∂canonicalBrownianMeasure)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (bound:=fun sample=>Real.exp (2*β^2+2*|β| *‖canonicalBrownianPath sample‖)*‖ψ‖)
  · exact .of_forall fun i=>((measurable_scalarPrefixLikelihood β (ν i) t).mul
      (ψ.continuous.measurable.comp (measurable_scalarStoppedBrownianPath β t))).aestronglyMeasurable
  · exact .of_forall fun i=>.of_forall fun sample=>by
      rw [norm_mul]
      exact mul_le_mul (scalarPrefixLikelihood_envelope β (ν i) t ht sample)
        (ψ.norm_coe_le_norm _) (norm_nonneg _) (Real.exp_pos _).le
  · have hi := ((integrable_exp_norm_canonicalBrownianPath (2*|β|)).const_mul
      (Real.exp (2*β^2))).mul_const ‖ψ‖
    convert hi using 1
    funext sample
    rw [←Real.exp_add]
  · exact .of_forall fun sample=>(tendsto_scalarPrefixLikelihood_of_weak β μ ν hν t ht sample).mul_const _

/-- The source prefix law, including arbitrary atomic and non-atomic profiles,
as an equality of measures on the entire continuous stopped history. -/
theorem scalarStoppedPath_likelihood (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (t : ℝ≥0) (ht : (t:ℝ)≤1) :
    canonicalBrownianMeasure.map (scalarStoppedStatePath β μ t)=
      (canonicalBrownianMeasure.withDensity (forwardBrownianWeight β μ t)).map
        (scalarStoppedBrownianPath β t) := by
  let ν : ℕ→Paper.ParisiMeasure := preservingMeasure μ ∅
  have hν : Tendsto ν atTop (𝓝 μ) := tendsto_preservingMeasure μ ∅
  letI := isFiniteMeasure_scalarPrefixReference β μ t ht
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro ψ
  rw [integral_map_of_stronglyMeasurable (measurable_scalarStoppedStatePath β hβ μ t ht)
    ψ.continuous.measurable.stronglyMeasurable,
      integral_scalarStoppedBrownianPath_withDensity]
  have he (n : ℕ) :
      (∫sample,ψ (scalarStoppedStatePath β (ν n) t sample) ∂canonicalBrownianMeasure)=
        ∫sample,scalarPrefixLikelihood β (ν n) t sample *
          ψ (scalarStoppedBrownianPath β t sample) ∂canonicalBrownianMeasure := by
    have hm := scalarStoppedPath_likelihood_finite β hβ (ν n)
      (finite_support_preservingMeasure μ ∅ n) t ht
    have h := congrArg (fun Q : Measure C(Paper.Overlap,ℝ)=>∫p,ψ p ∂Q) hm
    rw [integral_map_of_stronglyMeasurable (measurable_scalarStoppedStatePath β hβ (ν n) t ht)
      ψ.continuous.measurable.stronglyMeasurable,
        integral_scalarStoppedBrownianPath_withDensity] at h
    exact h
  exact tendsto_nhds_unique (tendsto_integral_scalarStoppedStatePath_of_weak β hβ μ ν hν t ht ψ)
    ((tendsto_integral_scalarPrefixObservable_of_weak β μ ν hν t ht ψ).congr' (.of_forall fun n=>(he n).symm))

end HexagonPaper
