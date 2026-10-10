module
public import QuantitativeFollowup.ScalarFiniteHistoryExponential

@[expose] public section

/-! The constructed scalar diffusion and its terminal spin have the literal
finite Gaussian density used in the transport-response calculation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem measurable_scalarFiniteHistoryDensity (s : RSBScheme k) (β : ℝ) :
    Measurable (scalarFiniteHistoryDensity s β) := by
  have hp : Measurable (fun p : (Fin (k+3)→ℝ)×Bool =>
      FRSB.finiteHistoryDensity (FRSB.forwardSchemeWeight s β 1) (k+2) p.1) :=
    (FRSB.measurable_finiteHistoryDensity _
    (FRSB.measurable_forwardSchemeWeight s β 1) (k+2)).comp measurable_fst
  have hs := measurable_scalarSpinMarkWeight
    (fun h : Fin (k+3)→ℝ => h (Fin.last (k+2))) (measurable_pi_apply _)
  convert hp.mul hs using 1
  funext p
  exact (scalarFiniteHistory_transition_spin_density s β p).symm

/-- Exact marked density relative to the actual unweighted Brownian history
and counting measure. The initial and every zero-variance node are retained. -/
theorem scalarMarkedSpinLaw_history_density (s : RSBScheme k) (β : ℝ) (hβ : β≠0) :
    (scalarMarkedSpinLaw β hβ (Paper.parisiSchemeMeasure s)).map
      (fun p => (scalarSelectedHistory s β hβ p.1,p.2))=
    ((Paper.canonicalBrownianMeasure.map
      (FRSB.historySample (fun r ω => β*Paper.canonicalBrownian r ω)
        (FRSB.forwardSchemeTime s 1) (k+2))).prod (Measure.count : Measure Bool)).withDensity
      (scalarFiniteHistoryDensity s β) := by
  rw [scalarMarkedSpinLaw_history_map]
  have he : scalarHistorySpinKernel (k+2)=
      (Kernel.const (Fin (k+3)→ℝ) (Measure.count : Measure Bool)).withDensity
        (fun h e => ENNReal.ofReal (scalarSpinWeight (h (Fin.last (k+2))) e)) :=
    scalarSpinMarkKernel_eq_withDensity _ _
  haveI : IsSFiniteKernel ((Kernel.const (Fin (k+3)→ℝ) (Measure.count : Measure Bool)).withDensity
      (fun h e => ENNReal.ofReal (scalarSpinWeight (h (Fin.last (k+2))) e))) := by
    rw [←he]
    infer_instance
  change (Paper.canonicalBrownianMeasure.map
    (FRSB.historySample (Paper.selectedParisiItoState β 0 hβ (Paper.parisiSchemeMeasure s))
      (FRSB.forwardSchemeTime s 1) (k+2))) ⊗ₘ scalarHistorySpinKernel (k+2)=_
  rw [FRSB.selectedState_history_eq_tiltedBrownian s β hβ 1 (by norm_num) (k+2),he,
    Measure.withDensity_compProd_withDensity
      (FRSB.measurable_finiteHistoryDensity _ (FRSB.measurable_forwardSchemeWeight s β 1) (k+2))
      (show Measurable (Function.uncurry (fun h : Fin (k+3)→ℝ => fun e : Bool =>
        ENNReal.ofReal (scalarSpinWeight (h (Fin.last (k+2))) e))) from
          measurable_scalarSpinMarkWeight (fun h : Fin (k+3)→ℝ => h (Fin.last (k+2)))
            (measurable_pi_apply _)),Measure.compProd_const]
  congr 1
  funext p
  exact scalarFiniteHistory_transition_spin_density s β p

def scalarGaussianHistoryMarkMap (s : RSBScheme k) (β : ℝ) :
    (QuantitativePaper.Field (k+2)×Bool)→((Fin (k+3)→ℝ)×Bool) :=
  fun p => (scalarGaussianHistoryLinear β (FRSB.forwardSchemeTime s 1) (k+2) p.1,p.2)

theorem measurable_scalarGaussianHistoryMarkMap (s : RSBScheme k) (β : ℝ) :
    Measurable (scalarGaussianHistoryMarkMap s β) :=
  ((scalarGaussianHistoryLinear β (FRSB.forwardSchemeTime s 1) (k+2)).measurable.comp measurable_fst).prodMk measurable_snd

def scalarGaussianMarkedLaw (s : RSBScheme k) (β : ℝ) : Measure (QuantitativePaper.Field (k+2)×Bool) :=
  ((fieldGaussian (k+2)).prod (Measure.count : Measure Bool)).withDensity
    (fun p => scalarFiniteHistoryDensity s β (scalarGaussianHistoryMarkMap s β p))

/-- Explicit independent Euclidean Gaussian coordinates, with their exact
marked density, reproduce the actual diffusion/spin finite law. -/
theorem scalarGaussianMarkedLaw_map (s : RSBScheme k) (β : ℝ) (hβ : β≠0) :
    (scalarGaussianMarkedLaw s β).map (scalarGaussianHistoryMarkMap s β)=
    (scalarMarkedSpinLaw β hβ (Paper.parisiSchemeMeasure s)).map
      (fun p => (scalarSelectedHistory s β hβ p.1,p.2)) := by
  rw [scalarMarkedSpinLaw_history_density s β hβ,
    scaledBrownian_history_eq_gaussianLinear β _
      (FRSB.forwardSchemeTime_monotone s 1) (FRSB.forwardSchemeTime_zero s 1) (k+2)]
  have he : ((fieldGaussian (k+2)).map
      (scalarGaussianHistoryLinear β (FRSB.forwardSchemeTime s 1) (k+2))).prod
      (Measure.count : Measure Bool)=
      (((fieldGaussian (k+2)).prod (Measure.count : Measure Bool)).map
        (scalarGaussianHistoryMarkMap s β)) := by
    conv_lhs => rhs;rw [←Measure.map_id (μ := (Measure.count : Measure Bool))]
    exact Measure.map_prod_map _ _ (scalarGaussianHistoryLinear β (FRSB.forwardSchemeTime s 1) (k+2)).measurable measurable_id
  rw [he]
  exact map_withDensity_pullback _ _ (measurable_scalarGaussianHistoryMarkMap s β) _
    (measurable_scalarFiniteHistoryDensity s β)

theorem isProbabilityMeasure_scalarGaussianMarkedLaw (s : RSBScheme k) (β : ℝ) (hβ : β≠0) :
    IsProbabilityMeasure (scalarGaussianMarkedLaw s β) := by
  apply (Measure.isProbabilityMeasure_map_iff
    (measurable_scalarGaussianHistoryMarkMap s β).aemeasurable).mp
  rw [scalarGaussianMarkedLaw_map s β hβ]
  infer_instance

/-- Every measurable retained-history observable has the same actual integral,
not only the terminal spin or a selected polynomial moment. -/
theorem integral_scalarGaussianMarkedLaw_history (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (f : ((Fin (k+3)→ℝ)×Bool)→ℝ) (hf : Measurable f) :
    (∫p,f (scalarGaussianHistoryMarkMap s β p) ∂scalarGaussianMarkedLaw s β)=
      ∫p,f (scalarSelectedHistory s β hβ p.1,p.2)
        ∂scalarMarkedSpinLaw β hβ (Paper.parisiSchemeMeasure s) := by
  rw [←integral_map (measurable_scalarGaussianHistoryMarkMap s β).aemeasurable
      hf.aestronglyMeasurable,scalarGaussianMarkedLaw_map s β hβ]
  exact integral_map ((measurable_scalarSelectedHistory s β hβ).comp measurable_fst |>.prodMk
    measurable_snd).aemeasurable hf.aestronglyMeasurable

end QuantitativeFollowup
