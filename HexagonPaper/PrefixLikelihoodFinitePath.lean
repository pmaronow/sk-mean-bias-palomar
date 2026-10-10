module
public import HexagonPaper.PrefixLikelihoodPathExt
public import OverlapPaper.ScalarFiniteObservationScheme
public import FRSB.FiniteForwardEndpoint
public import FRSB.ForwardStateLawLimit

@[expose] public section

/-! The exact prefix likelihood on the full continuous stopped path space
for every finite-support profile. Every observation family is inserted with
zero mass into a scheme carrying the identical profile measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open QuantitativeFollowup SpinGlass.Targets
open scoped NNReal ENNReal Topology
namespace HexagonPaper
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def scalarStoppedStatePath (β : ℝ) (μ : Paper.ParisiMeasure) (t : ℝ≥0)
    (sample : Paper.BrownianSample) : C(Paper.Overlap,ℝ) :=
  ⟨fun q=>optimalStateReal β μ sample (min (q:ℝ) t),
    (continuous_optimalStateReal β μ sample).comp
      (continuous_subtype_val.min continuous_const)⟩

def scalarStoppedBrownianPath (β : ℝ) (t : ℝ≥0)
    (sample : Paper.BrownianSample) : C(Paper.Overlap,ℝ) :=
  ⟨fun q=>β*canonicalBrownian (stoppedOverlapTime t q) sample,
    ((continuous_canonicalBrownian sample).comp
      (show Continuous (stoppedOverlapTime t) from
        (continuous_subtype_val.min continuous_const).subtype_mk _)).const_mul β⟩

theorem measurable_scalarStoppedStatePath (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (t : ℝ≥0) (ht : (t:ℝ)≤1) :
    Measurable (scalarStoppedStatePath β μ t) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro q
  exact measurable_optimalStateReal_time β hβ μ
    ⟨le_min q.property.1 t.coe_nonneg,(min_le_right _ _).trans ht⟩

theorem measurable_scalarStoppedBrownianPath (β : ℝ) (t : ℝ≥0) :
    Measurable (scalarStoppedBrownianPath β t) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro q
  exact (measurable_canonicalBrownian (stoppedOverlapTime t q)).const_mul β

private theorem forwardSchemeTime_node {k : ℕ} (s : RSBScheme k)
    (t : ℝ≥0) (i : Fin (k+3)) :
    forwardSchemeTime s t i=stoppedOverlapTime t (scalarSchemeTransportNode s i) := by
  apply NNReal.eq
  change min (s.q (min (i:ℕ) (k+2))) (t:ℝ)=min (scalarSchemeTransportNode s i : ℝ) (t:ℝ)
  rw [min_eq_left (by have := i.isLt;omega : (i:ℕ)≤k+2),
    scalarSchemeTransportNode_coe s i (by have := i.isLt;omega)]

theorem scalarStoppedPath_finiteObservations_likelihood
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (hμ : (μ : Measure Paper.Overlap).support.Finite)
    (t : ℝ≥0) (ht : (t:ℝ)≤1) (S : Finset Paper.Overlap) :
    canonicalBrownianMeasure.map
      (fun sample=>S.restrict (scalarStoppedStatePath β μ t sample)) =
      (canonicalBrownianMeasure.withDensity (forwardBrownianWeight β μ t)).map
        (fun sample=>S.restrict (scalarStoppedBrownianPath β t sample)) := by
  obtain ⟨K,s,j,hs,hj⟩ := OverlapPaper.exists_finiteLaw_scheme_observation_family μ hμ
    (fun q : S=>(q : Paper.Overlap))
  let Y := FRSB.historySample (fun r sample=>β*canonicalBrownian r sample)
    (forwardSchemeTime s t) (K+2)
  let V := FRSB.historySample (selectedParisiItoState β 0 hβ μ)
    (forwardSchemeTime s t) (K+2)
  let L : (Fin (K+3)→ℝ)→(S→ℝ) := fun p q=>p (j q)
  let D := FRSB.finiteHistoryDensity (forwardSchemeWeight s β t) (K+2)
  have hY : Measurable Y := FRSB.measurable_historySample _
    (fun r=>(measurable_canonicalBrownian r).const_mul β) _ _
  have hV : Measurable V := FRSB.measurable_historySample _
    (measurable_selectedParisiState_time β 0 hβ μ) _ _
  have hL : Measurable L := Measurable.of_eval (fun q=>measurable_pi_apply (j q))
  have hD : Measurable D := FRSB.measurable_finiteHistoryDensity _
    (measurable_forwardSchemeWeight s β t) _
  have he := selectedState_history_eq_tiltedBrownian s β hβ t ht (K+2)
  rw [hs] at he
  change canonicalBrownianMeasure.map V=(canonicalBrownianMeasure.map Y).withDensity D at he
  rw [←FRSB.map_withDensity_pullback _ Y hY D hD] at he
  have hweight : (fun sample=>D (Y sample))=forwardBrownianWeight β μ t := by
    funext sample
    simpa only [D,Y,hs] using finiteHistoryDensity_eq_forwardBrownianWeight s β t ht sample
  rw [hweight] at he
  have he' := congrArg (fun Q : Measure (Fin (K+3)→ℝ)=>Q.map L) he
  rw [Measure.map_map hL hV,Measure.map_map hL hY] at he'
  have htime (q : S) : forwardSchemeTime s t (j q)=stoppedOverlapTime t q := by
    rw [forwardSchemeTime_node,hj q]
  have hleft : L∘V=fun sample=>S.restrict (scalarStoppedStatePath β μ t sample) := by
    funext sample q
    change selectedParisiItoState β 0 hβ μ (forwardSchemeTime s t (j q)) sample=_
    rw [htime]
    change optimalState β μ (stoppedOverlapTime t q) sample=optimalStateReal β μ sample _
    exact optimalState_eq_real β μ
      (by change min (q:ℝ) t≤1;exact (min_le_right _ _).trans ht) sample
  have hright : L∘Y=fun sample=>S.restrict (scalarStoppedBrownianPath β t sample) := by
    funext sample q
    change β*canonicalBrownian (forwardSchemeTime s t (j q)) sample=_
    rw [htime];rfl
  rw [hleft,hright] at he'
  exact he'

theorem scalarStoppedPath_likelihood_finite
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (hμ : (μ : Measure Paper.Overlap).support.Finite)
    (t : ℝ≥0) (ht : (t:ℝ)≤1) :
    canonicalBrownianMeasure.map (scalarStoppedStatePath β μ t)=
      (canonicalBrownianMeasure.withDensity (forwardBrownianWeight β μ t)).map
        (scalarStoppedBrownianPath β t) := by
  apply continuousPathMeasure_ext
  intro S
  have hm : Measurable (fun p : C(Paper.Overlap,ℝ)=>S.restrict p) :=
    Measurable.of_eval (fun q=>ContinuousMap.measurable_eval (q:Paper.Overlap))
  rw [Measure.map_map hm (measurable_scalarStoppedStatePath β hβ μ t ht),
    Measure.map_map hm (measurable_scalarStoppedBrownianPath β t)]
  exact scalarStoppedPath_finiteObservations_likelihood β hβ μ hμ t ht S

end HexagonPaper
