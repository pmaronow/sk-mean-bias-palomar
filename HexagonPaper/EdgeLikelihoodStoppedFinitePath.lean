module
public import HexagonPaper.EdgeLikelihoodStoppedHistoryAction
public import OverlapPaper.ScalarFiniteObservationScheme

@[expose] public section

/-! Actual finite-profile likelihood on the entire continuous stopped edge
path. Observation refinements retain every observation and the stopping
time without changing the measure; the chronological history is stopped
by the genuine deterministic prefix extension. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup SpinGlass.Targets
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

private theorem edge_scheme_node_min {k : ℕ} (s : RSBScheme k) (i H : ℕ)
    (hi : i≤k+2) (hH : H≤k+2) : s.q (min i H)=min (s.q i) (s.q H) := by
  by_cases h : i≤H
  · rw [min_eq_left h,min_eq_left (s.q_mono' H hH i h)]
  · rw [min_eq_right (le_of_not_ge h),min_eq_right (s.q_mono' i hi H (le_of_not_ge h))]

theorem edge_stopped_finite_observations_likelihood (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (hμ : (μ:Measure Paper.Overlap).support.Finite)
    (g : AnisotropicDisorder n) (q h : Paper.Overlap) (hqh : q≤h)
    (x : Field n) (S : Finset Paper.Overlap) :
    (vectorDisorderBrownianMeasure n).map
        (fun sample=>S.restrict (edgeStoppedDiffusionPath D μ g q h x sample))=
      ((vectorDisorderBrownianMeasure n).withDensity
        (fun sample=>edgeStoppedLikelihood D μ q h (edgeStoppedReferencePath D g q h x sample))).map
          (fun sample=>S.restrict (edgeStoppedReferencePath D g q h x sample)) := by
  let T:Option S→Paper.Overlap:=fun r=>match r with | none=>h | some r=>(r:Paper.Overlap)
  obtain ⟨K,s,j,hs,hj⟩:=OverlapPaper.exists_finiteLaw_scheme_observation_family μ hμ T
  let H:ℕ:=j none
  have hH : H≤K+2:=by have:= (j none).isLt;omega
  have hstop : s.q H=(h:ℝ) := by
    have hn:=congrArg Subtype.val (hj none)
    simpa only [scalarSchemeTransportNode_coe s (j none) hH,T] using hn
  let Y:=edgeStoppedReferenceHistory D s g q x H (K+2) hH
  let V:=edgeStoppedPhysicalHistory D s g q x H (K+2) hH
  let L:FiniteHistory (AnisotropicParameter n) (K+2)→(S→AnisotropicParameter n):=
    fun p r=>p (j (some r))
  let w:=finiteHistoryDensity (edgeRestartFiniteWeight D s q) H ∘edgeHistoryStopRestrict H (K+2) hH
  have hY : Measurable Y:=(measurable_edgeHistoryStopExtend H (K+2) hH).comp
    (measurable_edgeReferenceBrownianHistory D s g q x H)
  have hV : Measurable V:=(measurable_edgeHistoryStopExtend H (K+2) hH).comp
    (measurable_anisotropicFiniteRestartPhysicalHistory D s g q x H)
  have hL : Measurable L:=Measurable.of_eval (fun r=>measurable_pi_apply (j (some r)))
  have hw : Measurable w:=(measurable_finiteHistoryDensity _
    (fun i=>measurable_anisotropicFiniteTransitionWeight D (vectorClampedScheme s q q.property) (i+1)) H).comp
      (measurable_edgeHistoryStopRestrict H (K+2) hH)
  have he:=edge_stopped_finite_history_likelihood D s g q x H (K+2) hH hH
  change (vectorDisorderBrownianMeasure n).map V=
    ((vectorDisorderBrownianMeasure n).map Y).withDensity w at he
  rw [←map_withDensity_pullback _ Y hY w hw] at he
  have hweight : (fun sample=>w (Y sample))=
      (fun sample=>edgeStoppedLikelihood D μ q h (edgeStoppedReferencePath D g q h x sample)) := by
    funext sample
    dsimp only [w,Y,edgeStoppedReferenceHistory,Function.comp_def]
    rw [edgeHistoryStopRestrict_extend]
    rw [edge_stopped_finite_reference_density_action D s g q h hqh x H hH hstop sample,hs]
    exact (edgeStoppedLikelihood_stop D μ q h _).symm
  rw [hweight] at he
  have he':=congrArg (fun Q:Measure (FiniteHistory (AnisotropicParameter n) (K+2))=>Q.map L) he
  rw [Measure.map_map hL hV,Measure.map_map hL hY] at he'
  have htime (r : S) :
      anisotropicRestartElapsed s q (min (j (some r):ℕ) H)=
        (((edgeStopOverlap h r:Paper.Overlap):ℝ)-(q:ℝ)).toNNReal := by
    have hi : (j (some r):ℕ)≤K+2:=by have:=(j (some r)).isLt;omega
    have hn:=congrArg Subtype.val (hj (some r))
    rw [scalarSchemeTransportNode_coe s _ hi] at hn
    change s.q (j (some r))=(r:ℝ) at hn
    unfold anisotropicRestartElapsed
    rw [edge_scheme_node_min s _ H hi hH,hn,hstop]
    change (max (q:ℝ) (min (r:ℝ) h)-(q:ℝ)).toNNReal=(min (r:ℝ) h-(q:ℝ)).toNNReal
    by_cases ht : (q:ℝ) ≤ min (r:ℝ) h
    · rw [max_eq_right ht]
    · rw [max_eq_left (le_of_not_ge ht),sub_self,Real.toNNReal_zero,
        Real.toNNReal_eq_zero.mpr (sub_nonpos.mpr (le_of_not_ge ht))]
  have hleft : L∘V=(fun sample=>S.restrict (edgeStoppedDiffusionPath D μ g q h x sample)) := by
    funext sample r
    change anisotropicDisorderInjection n g+anisotropicUnitInput D
      (anisotropicFiniteRestartState D s g q x
        (anisotropicRestartElapsed s q (min (j (some r):ℕ) H)) sample)=_
    rw [←anisotropicRestartState_scheme_eq_finite,hs,htime]
    rfl
  have hright : L∘Y=(fun sample=>S.restrict (edgeStoppedReferencePath D g q h x sample)) := by
    funext sample r
    change anisotropicDisorderInjection n g+anisotropicUnitInput D x+
      anisotropicUnitInput D (disorderVectorBrownian
        (anisotropicRestartElapsed s q (min (j (some r):ℕ) H)) sample)=_
    rw [htime]
    rfl
  rw [hleft,hright] at he'
  exact he'

theorem edge_stopped_continuous_path_likelihood_finite (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (hμ : (μ:Measure Paper.Overlap).support.Finite)
    (g : AnisotropicDisorder n) (q h : Paper.Overlap) (hqh : q≤h) (x : Field n) :
    (vectorDisorderBrownianMeasure n).map (edgeStoppedDiffusionPath D μ g q h x)=
      ((vectorDisorderBrownianMeasure n).withDensity
        (fun sample=>edgeStoppedLikelihood D μ q h (edgeStoppedReferencePath D g q h x sample))).map
          (edgeStoppedReferencePath D g q h x) := by
  apply continuousPathMeasure_ext
  intro S
  have hm : Measurable (fun p:C(Paper.Overlap,AnisotropicParameter n)=>S.restrict p):=
    Measurable.of_eval (fun r=>ContinuousMap.measurable_eval (r:Paper.Overlap))
  rw [Measure.map_map hm (measurable_edgeStoppedDiffusionPath D μ g q h x),
    Measure.map_map hm (measurable_edgeStoppedReferencePath D g q h x)]
  exact edge_stopped_finite_observations_likelihood D μ hμ g q h hqh x S

end HexagonPaper
