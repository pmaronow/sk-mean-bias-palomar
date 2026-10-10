module
public import HexagonPaper.EdgeLikelihoodAction
public import HexagonPaper.PrefixLikelihoodPathExt
public import OverlapPaper.ScalarFiniteObservationScheme
public import QuantitativeFollowup.AnisotropicFiniteMeasureStateAgreement

@[expose] public section

/-! Actual full continuous-path suffix likelihood for every finite-support
profile. Refinement retains any prescribed observations with identical
profile measure; the result is a path measure equality, not a finite-grid
likelihood premise. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup SpinGlass.Targets
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def edgeReferencePath (D : AnisotropicSpinModel n) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n) :
    C(Paper.Overlap,AnisotropicParameter n) :=
  ⟨edgeReferenceParameter D g q x sample,
    continuous_const.add ((anisotropicUnitInput D).continuous.comp
      ((continuous_disorderVectorBrownian sample).comp
        (continuous_real_toNNReal.comp (continuous_subtype_val.sub continuous_const))))⟩

def edgeDiffusionPath (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (sample : VectorDisorderBrownianSample n) : C(Paper.Overlap,AnisotropicParameter n) :=
  ⟨fun r => anisotropicDisorderInjection n g+anisotropicUnitInput D
      (anisotropicRestartState D μ g q x ((r:ℝ)-(q:ℝ)).toNNReal sample),
    continuous_const.add ((anisotropicUnitInput D).continuous.comp
      ((continuous_anisotropicRestartState D μ g q x sample).comp
        (continuous_real_toNNReal.comp (continuous_subtype_val.sub continuous_const))))⟩

theorem measurable_edgeReferencePath (D : AnisotropicSpinModel n)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    Measurable (edgeReferencePath D g q x) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro r
  exact measurable_const.add ((anisotropicUnitInput D).continuous.measurable.comp
    (measurable_disorderVectorBrownian _))

theorem measurable_edgeDiffusionPath (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    Measurable (edgeDiffusionPath D μ g q x) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro r
  change Measurable (fun sample : VectorDisorderBrownianSample n =>
    anisotropicDisorderInjection n g+anisotropicUnitInput D
      (anisotropicRestartState D μ g q x ((r:ℝ)-(q:ℝ)).toNNReal sample))
  have hm : Measurable (anisotropicRestartState D μ g q x ((r:ℝ)-(q:ℝ)).toNNReal) :=
    (stronglyAdapted_anisotropicRestartState D μ g q x _).measurable.mono
      ((vectorBrownianFiltration n).le _) le_rfl
  exact measurable_const.add ((anisotropicUnitInput D).continuous.measurable.comp
    hm)

private theorem restartElapsed_observation_node {k : ℕ} (s : RSBScheme k)
    (q : Paper.Overlap) (i : Fin (k+3)) :
    anisotropicRestartElapsed s q i=
      ((scalarSchemeTransportNode s i:ℝ)-(q:ℝ)).toNNReal := by
  have hi : (i:ℕ)≤k+2:=by omega
  rw [scalarSchemeTransportNode_coe s i hi]
  unfold anisotropicRestartElapsed
  by_cases h : (q:ℝ) ≤ s.q i
  · rw [max_eq_right h]
  · rw [max_eq_left (le_of_not_ge h),sub_self,Real.toNNReal_zero,
      Real.toNNReal_eq_zero.mpr (sub_nonpos.mpr (le_of_not_ge h))]

theorem edge_suffix_finite_observations_likelihood
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (hμ : (μ:Measure Paper.Overlap).support.Finite)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (S : Finset Paper.Overlap) :
    (vectorDisorderBrownianMeasure n).map
        (fun sample=>S.restrict (edgeDiffusionPath D μ g q x sample))=
      ((vectorDisorderBrownianMeasure n).withDensity
        (fun sample=>edgeSuffixLikelihood D μ q (edgeReferencePath D g q x sample))).map
          (fun sample=>S.restrict (edgeReferencePath D g q x sample)) := by
  obtain ⟨K,s,j,hs,hj⟩:=OverlapPaper.exists_finiteLaw_scheme_observation_family μ hμ
    (fun r : S=>(r:Paper.Overlap))
  let Y:=edgeReferenceBrownianHistory D s g q x (K+2)
  let V:=anisotropicFiniteRestartPhysicalHistory D s g q x (K+2)
  let L : FiniteHistory (AnisotropicParameter n) (K+2) → (S→AnisotropicParameter n) :=
    fun p r=>p (j r)
  let w:=finiteHistoryDensity (edgeRestartFiniteWeight D s q) (K+2)
  have hY:=measurable_edgeReferenceBrownianHistory D s g q x (K+2)
  have hV:=measurable_anisotropicFiniteRestartPhysicalHistory D s g q x (K+2)
  have hL : Measurable L:=Measurable.of_eval (fun r=>measurable_pi_apply (j r))
  have hw : Measurable w:=measurable_finiteHistoryDensity _
    (fun i=>measurable_anisotropicFiniteTransitionWeight D (vectorClampedScheme s q q.property) (i+1)) _
  have he:=edge_restart_finite_brownian_likelihood D s g q x (K+2) le_rfl
  change (vectorDisorderBrownianMeasure n).map V=
    ((vectorDisorderBrownianMeasure n).map Y).withDensity w at he
  rw [←map_withDensity_pullback _ Y hY w hw] at he
  have hweight : (fun sample=>w (Y sample))=
      (fun sample=>edgeSuffixLikelihood D μ q (edgeReferencePath D g q x sample)) := by
    funext sample
    simpa only [w,Y,hs,edgeReferencePath,ContinuousMap.coe_mk] using
      edge_restart_finite_reference_density_action D s g q x sample
  rw [hweight] at he
  have he':=congrArg (fun Q : Measure (FiniteHistory (AnisotropicParameter n) (K+2))=>Q.map L) he
  rw [Measure.map_map hL hV,Measure.map_map hL hY] at he'
  have htime (r : S) : anisotropicRestartElapsed s q (j r)=
      (((r:Paper.Overlap):ℝ)-(q:ℝ)).toNNReal := by
    rw [restartElapsed_observation_node,hj r]
  have hleft : L∘V=(fun sample=>S.restrict (edgeDiffusionPath D μ g q x sample)) := by
    funext sample r
    change anisotropicDisorderInjection n g+anisotropicUnitInput D
      (anisotropicFiniteRestartState D s g q x (anisotropicRestartElapsed s q (j r)) sample)=_
    rw [←anisotropicRestartState_scheme_eq_finite,hs,htime]
    rfl
  have hright : L∘Y=(fun sample=>S.restrict (edgeReferencePath D g q x sample)) := by
    funext sample r
    change anisotropicDisorderInjection n g+anisotropicUnitInput D x+
      anisotropicUnitInput D (disorderVectorBrownian (anisotropicRestartElapsed s q (j r)) sample)=_
    rw [htime]
    rfl
  rw [hleft,hright] at he'
  exact he'

theorem edge_suffix_continuous_path_likelihood_finite
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (hμ : (μ:Measure Paper.Overlap).support.Finite)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    (vectorDisorderBrownianMeasure n).map (edgeDiffusionPath D μ g q x)=
      ((vectorDisorderBrownianMeasure n).withDensity
        (fun sample=>edgeSuffixLikelihood D μ q (edgeReferencePath D g q x sample))).map
          (edgeReferencePath D g q x) := by
  apply continuousPathMeasure_ext
  intro S
  have hm : Measurable (fun p : C(Paper.Overlap,AnisotropicParameter n)=>S.restrict p) :=
    Measurable.of_eval (fun r=>ContinuousMap.measurable_eval (r:Paper.Overlap))
  rw [Measure.map_map hm (measurable_edgeDiffusionPath D μ g q x),
    Measure.map_map hm (measurable_edgeReferencePath D g q x)]
  exact edge_suffix_finite_observations_likelihood D μ hμ g q x S

end HexagonPaper
