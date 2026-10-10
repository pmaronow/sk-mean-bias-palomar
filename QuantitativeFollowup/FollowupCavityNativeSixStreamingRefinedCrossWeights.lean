module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSelectedCrossPatternMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternVertexCoherenceCrossOrigin
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedCrossWeightsEndpoint
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedDiscreteChargeGrouping

@[expose] public section

/-! Actual double attachment charges under an observation refinement.
The marked-law callbacks are genuine projected terminal moments; both
Stieltjes weights belong to the original tree. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem refinedCross_root_coherent_add {j : ℕ}
    (T : FiniteTerminalGenealogy j) (f g : FiniteCascadeRecordVertex T → ℝ)
    (hf : nativeStreamingRootCoherent T f) (hg : nativeStreamingRootCoherent T g) :
    nativeStreamingRootCoherent T (fun v => f v+g v) := by
  induction T with
  | leaf => trivial
  | advance T ih => exact ih _ _ hf hg
  | fork T U ihT ihU =>
      exact ⟨congrArg₂ (·+·) hf.1 hg.1,congrArg₂ (·+·) hf.2.1 hg.2.1,
        ihT _ _ hf.2.2.1 hg.2.2.1,ihU _ _ hf.2.2.2 hg.2.2.2⟩

private theorem refinedCross_root_coherent_mul {j : ℕ}
    (T : FiniteTerminalGenealogy j) (c : ℝ) (f : FiniteCascadeRecordVertex T → ℝ)
    (hf : nativeStreamingRootCoherent T f) :
    nativeStreamingRootCoherent T (fun v => c*f v) := by
  induction T with
  | leaf => trivial
  | advance T ih => exact ih _ hf
  | fork T U ihT ihU =>
      exact ⟨congrArg (c*·) hf.1,congrArg (c*·) hf.2.1,
        ihT _ hf.2.2.1,ihU _ hf.2.2.2⟩

private theorem refinedCross_root_coherent_list {A : Type*} {j : ℕ}
    (T : FiniteTerminalGenealogy j) (L : List (ℝ × A))
    (f : FiniteCascadeRecordVertex T → A → ℝ)
    (hf : ∀w, nativeStreamingRootCoherent T (fun v => f v w)) :
    nativeStreamingRootCoherent T (fun v => (L.map (fun c => c.1*f v c.2)).sum) := by
  induction L with
  | nil => simpa only [List.map_nil,List.sum_nil] using nativeStreamingRootCoherent_const T 0
  | cons c L ih =>
      simp only [List.map_cons,List.sum_cons]
      exact refinedCross_root_coherent_add T _ _
        (refinedCross_root_coherent_mul T c.1 _ (hf c.2)) ih

private theorem refinedCross_double_charge_root_coherent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (Q : ℕ → Paper.Overlap) (b : ℕ → ℝ) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingRootCoherent T (fun v => nativeStreamingVertexChargeSum b s T
      (fun w => nativeStreamingPatternMoment D μ a Q T F (.cross (.vertex v) (.vertex w)))) := by
  exact refinedCross_root_coherent_list T (finiteCascadeVertexCharges b s T) _
    (fun w => nativeStreamingPatternMoment_cross_left_vertex_root_coherent D μ a Q T F w)

private theorem refinedCross_coarse_antitone
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) : Antitone q := by
  intro i j hij
  rw [←hlevels i,←hlevels j]
  exact hQ ((observationRefinementDepth_strictMono d).monotone hij)

private theorem refinedCross_pattern_VV
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀i,Q (observationRefinementDepth d i)=q i) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v w : FiniteCascadeRecordVertex T) :
    nativeStreamingPatternMoment D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinedTerminalTest d T F)
      (.cross (.vertex (nativeStreamingRefinementVertexEmbed d T v))
        (.vertex (nativeStreamingRefinementVertexEmbed d T w)))=
      nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) (.vertex w)) := by
  have hq := refinedCross_coarse_antitone q Q d hQ hlevels
  have hQ0 : Q 0=1 := by simpa only [observationRefinementDepth] using (hlevels 0).trans hzero
  have hclock : nativeStreamingOriginCommonClock Q (observationRefineTree d T)
      (.vertex (nativeStreamingRefinementVertexEmbed d T v))
      (.vertex (nativeStreamingRefinementVertexEmbed d T w))=
      nativeStreamingOriginCommonClock q T (.vertex v) (.vertex w) := by
    simp only [nativeStreamingOriginCommonClock,
      nativeStreamingRefinementVertexEmbed_commonPathDepth,hlevels]
  simp only [nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment,hclock]
  rw [nativeStreamingOriginCrossProbability_vertex_vertex D μ a Q hQ hQ0,
    nativeStreamingOriginCrossProbability_vertex_vertex D μ a q hq hzero]
  simpa only [nativeStreamingDefectSpinTest,nativeStreamingRefinedTerminalTest,
    Function.comp_apply] using
    nativeStreamingCrossVertexTerminalIntegral_refinement D μ a q Q d hQ hlevels T v w
      (nativeStreamingDefectSpinTest T F (nativeStreamingOriginCommonClock q T (.vertex v) (.vertex w)))

private theorem refinedCross_originIntegral_congr
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (incoming : ℝ)
    (Φ Ψ : NativeStreamingOrigin T → ℝ)
    (hv : ∀v, Φ (.vertex v)=Ψ (.vertex v))
    (he : ∀(e : NativeStreamingEdge T) r,
      q (e.depth+1)≤r ∧ r≤q e.depth → Φ (.edge e r)=Ψ (.edge e r)) :
    nativeStreamingOriginWeightIntegral μ a q T incoming Φ =
      nativeStreamingOriginWeightIntegral μ a q T incoming Ψ := by
  induction T generalizing incoming with
  | leaf => simp only [nativeStreamingOriginWeightIntegral,hv]
  | @advance j T ih =>
      simp only [nativeStreamingOriginWeightIntegral]
      rw [ih _ (fun o => Φ (nativeStreamingOriginChild o))
        (fun o => Ψ (nativeStreamingOriginChild o))
        (fun v => hv (.child v)) (fun e r hr => he (.child e) r hr),hv]
      have hi : (∫r in Ioc (q (j+1)) (q j), Φ (.edge (.here T) r) ∂parisiFreeMeasure μ a) =
          ∫r in Ioc (q (j+1)) (q j), Ψ (.edge (.here T) r) ∂parisiFreeMeasure μ a :=
        setIntegral_congr_fun measurableSet_Ioc (fun r hr => he (.here T) r ⟨hr.1.le,hr.2⟩)
      rw [hi]
  | @fork j T U ihT ihU =>
      simp only [nativeStreamingOriginWeightIntegral]
      rw [ihT _ (fun o => Φ (nativeStreamingOriginLeft o))
        (fun o => Ψ (nativeStreamingOriginLeft o))
        (fun v => hv (.left v)) (fun e r hr => he (.left e) r hr),
        ihU _ (fun o => Φ (nativeStreamingOriginRight o))
        (fun o => Ψ (nativeStreamingOriginRight o))
        (fun v => hv (.right v)) (fun e r hr => he (.right e) r hr),hv]

private theorem refinedCross_scheme_zero
    (t : SpinGlass.Targets.RSBScheme k) (q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hlevels : ∀i, anisotropicRecordedSchemeSchedule (cdfMassScheme t)
      (observationRefinementDepth d i)=q i) : q 0=1 := by
  rw [←hlevels 0]
  change anisotropicRecordedSchemeSchedule (cdfMassScheme t) 0=1
  apply Subtype.ext
  rw [anisotropicRecordedSchemeSchedule,Nat.sub_zero,
    anisotropicFiniteMeshNode_coe (cdfMassScheme t) _ le_rfl,(cdfMassScheme t).q_top]
  rfl

private theorem refinedCross_inner_vertex
    (D : AnisotropicSpinModel (n+1)) (t : SpinGlass.Targets.RSBScheme k)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : Paper.parisiSchemeMeasure (cdfMassScheme t)∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hlevels : ∀i, anisotropicRecordedSchemeSchedule (cdfMassScheme t)
      (observationRefinementDepth d i)=q i)
    (T : FiniteTerminalGenealogy J) (hdepth : observationRefinementDepth d J≤k+1)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (v : FiniteCascadeRecordVertex T) :
    let μ := Paper.parisiSchemeMeasure (cdfMassScheme t)
    let Q := anisotropicRecordedSchemeSchedule (cdfMassScheme t)
    let R := observationRefineTree d T
    nativeStreamingVertexChargeSum (anisotropicSchemeMass (cdfMassScheme t)) a R
      (fun w => nativeStreamingPatternMoment D μ a Q R (nativeStreamingRefinedTerminalTest d T F)
        (.cross (.vertex (nativeStreamingRefinementVertexEmbed d T v)) (.vertex w))) =
      nativeStreamingOriginWeightIntegral μ a q T a
        (fun o => nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) o)) := by
  dsimp only
  let μ := Paper.parisiSchemeMeasure (cdfMassScheme t)
  let Q := anisotropicRecordedSchemeSchedule (cdfMassScheme t)
  have hQ := anisotropicRecordedSchemeSchedule_antitone (cdfMassScheme t)
  have hq := refinedCross_coarse_antitone q Q d hQ hlevels
  have hzero := refinedCross_scheme_zero t q d hlevels
  refine nativeStreamingNormalizedRefinedChargeSum_eq_originWeightIntegral t a ha hfloor q d hlevels
    T hdepth a _ _ ?_ ?_ ?_ ?_
  · exact nativeStreamingPatternMoment_cross_right_vertex_root_coherent D μ a Q _ _
      (nativeStreamingRefinementVertexEmbed d T v)
  · intro w
    exact refinedCross_pattern_VV D μ a q Q d hQ hlevels hzero T F v w
  · intro e p hp
    exact nativeStreamingPatternMoment_cross_VE_selected_refinement D μ a q Q d hQ hlevels hzero T F e p hp v
  · intro e
    exact nativeStreamingPatternMoment_cross_child_endpoint_edge D μ a q hq hzero T F v e

private theorem refinedCross_inner_selected
    (D : AnisotropicSpinModel (n+1)) (t : SpinGlass.Targets.RSBScheme k)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : Paper.parisiSchemeMeasure (cdfMassScheme t)∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    (hlevels : ∀i, anisotropicRecordedSchemeSchedule (cdfMassScheme t)
      (observationRefinementDepth d i)=q i)
    (T : FiniteTerminalGenealogy J) (hdepth : observationRefinementDepth d J≤k+1)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (p : ℕ) (hp : p<d e.depth) :
    let μ := Paper.parisiSchemeMeasure (cdfMassScheme t)
    let Q := anisotropicRecordedSchemeSchedule (cdfMassScheme t)
    let R := observationRefineTree d T
    nativeStreamingVertexChargeSum (anisotropicSchemeMass (cdfMassScheme t)) a R
      (fun w => nativeStreamingPatternMoment D μ a Q R (nativeStreamingRefinedTerminalTest d T F)
        (.cross (.vertex (nativeStreamingEdgeSelectedVertex d e p)) (.vertex w))) =
      nativeStreamingOriginWeightIntegral μ a q T a
        (fun o => nativeStreamingPatternMoment D μ a q T F
          (.cross (.edge e (Q (observationRefinementDepth d e.depth+p+1))) o)) := by
  dsimp only
  let μ := Paper.parisiSchemeMeasure (cdfMassScheme t)
  let Q := anisotropicRecordedSchemeSchedule (cdfMassScheme t)
  have hQ := anisotropicRecordedSchemeSchedule_antitone (cdfMassScheme t)
  have hq := refinedCross_coarse_antitone q Q d hQ hlevels
  have hzero := refinedCross_scheme_zero t q d hlevels
  have hlow : observationRefinementDepth d e.depth+p+1≤observationRefinementDepth d (e.depth+1) := by
    change observationRefinementDepth d e.depth+p+1≤observationRefinementDepth d e.depth+d e.depth+1
    omega
  have hhigh : observationRefinementDepth d e.depth≤observationRefinementDepth d e.depth+p+1 := by omega
  have hr : q (e.depth+1)≤Q (observationRefinementDepth d e.depth+p+1) ∧
      Q (observationRefinementDepth d e.depth+p+1)≤q e.depth := by
    rw [←hlevels (e.depth+1),←hlevels e.depth]
    exact ⟨hQ hlow,hQ hhigh⟩
  refine nativeStreamingNormalizedRefinedChargeSum_eq_originWeightIntegral t a ha hfloor q d hlevels
    T hdepth a _ _ ?_ ?_ ?_ ?_
  · exact nativeStreamingPatternMoment_cross_right_vertex_root_coherent D μ a Q _ _
      (nativeStreamingEdgeSelectedVertex d e p)
  · intro w
    exact nativeStreamingPatternMoment_cross_EV_selected_refinement D μ a q Q d hQ hlevels hzero T F e p hp w
  · intro f l hl
    exact nativeStreamingPatternMoment_cross_EE_selected_refinement D μ a q Q d hQ hlevels hzero T F e f p l hp hl
  · intro f
    exact nativeStreamingPatternMoment_cross_right_child_endpoint D μ a q hq hzero T F e f _ hr

theorem nativeStreamingRefinedCrossWeight_agreement
    (D : AnisotropicSpinModel (n+1)) (t : SpinGlass.Targets.RSBScheme k)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : Paper.parisiSchemeMeasure (cdfMassScheme t)∈scalarFloor a)
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (hdepth : observationRefinementDepth d J≤k+1)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    let μ := Paper.parisiSchemeMeasure (cdfMassScheme t)
    let Q := anisotropicRecordedSchemeSchedule (cdfMassScheme t)
    let q := fun i => Q (observationRefinementDepth d i)
    let R := observationRefineTree d T
    nativeStreamingVertexChargeSum (anisotropicSchemeMass (cdfMassScheme t)) a R
      (fun v => nativeStreamingVertexChargeSum (anisotropicSchemeMass (cdfMassScheme t)) a R
        (fun w => nativeStreamingPatternMoment D μ a Q R (nativeStreamingRefinedTerminalTest d T F)
          (.cross (.vertex v) (.vertex w)))) =
      nativeStreamingSourceCrossTerm D μ a q T F := by
  dsimp only
  let μ := Paper.parisiSchemeMeasure (cdfMassScheme t)
  let Q := anisotropicRecordedSchemeSchedule (cdfMassScheme t)
  let q := fun i => Q (observationRefinementDepth d i)
  let R := observationRefineTree d T
  have hlevels : ∀i, Q (observationRefinementDepth d i)=q i := fun _ => rfl
  have hQ := anisotropicRecordedSchemeSchedule_antitone (cdfMassScheme t)
  have hq := refinedCross_coarse_antitone q Q d hQ hlevels
  have hzero := refinedCross_scheme_zero t q d hlevels
  change _ = nativeStreamingOriginWeightIntegral μ a q T a (fun o =>
    nativeStreamingOriginWeightIntegral μ a q T a (fun p =>
      nativeStreamingPatternMoment D μ a q T F (.cross o p)))
  refine nativeStreamingNormalizedRefinedChargeSum_eq_originWeightIntegral t a ha hfloor q d hlevels
    T hdepth a _ _ ?_ ?_ ?_ ?_
  · exact refinedCross_double_charge_root_coherent D μ a Q
      (anisotropicSchemeMass (cdfMassScheme t)) a R (nativeStreamingRefinedTerminalTest d T F)
  · intro v
    exact refinedCross_inner_vertex D t a ha hfloor q d hlevels T hdepth F v
  · intro e p hp
    exact refinedCross_inner_selected D t a ha hfloor q d hlevels T hdepth F e p hp
  · intro e
    refine refinedCross_originIntegral_congr μ a q T a _ _ ?_ ?_
    · intro v
      exact nativeStreamingPatternMoment_cross_edge_child_endpoint D μ a q hq hzero T F e v
    · intro f l hl
      exact nativeStreamingPatternMoment_cross_left_child_endpoint D μ a q hq hzero T F e f l hl

end QuantitativeFollowup
