module
public import HexagonPaper.PathHeatWienerAnalyticSource
public import HexagonPaper.PathHeatTreeBernsteinFiniteCoordinatesJets

@[expose] public section

/-! Extend an actual native finite-coordinate/tree-path source to flat
row paths through a fixed coordinate restriction. Signed jets are true
measure pushforwards, so no derivatives in unused row levels are assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval NNReal
namespace HexagonPaper
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y E K : Type*}
  [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X] [CompactSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {a b : ℝ}

def pathHeatNativeSourceRestrictionState (ι : C(X,Y))
    (θ : Icc a b×((E×K)×C(Y,ℝ))) : Icc a b×((E×K)×C(X,ℝ)) :=
  (θ.1,(θ.2.1,pathHeatIndexRestriction ι θ.2.2))

theorem continuous_pathHeatNativeSourceRestrictionState (ι : C(X,Y)) :
    Continuous (pathHeatNativeSourceRestrictionState (a:=a) (b:=b) (E:=E) (K:=K) ι) := by
  exact continuous_fst.prodMk (continuous_snd.fst.prodMk
    ((pathHeatIndexRestriction ι).continuous.comp continuous_snd.snd))

def pathHeatNativeSourceExtension (ι : C(X,Y))
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(X,ℝ))) X) :
    PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Y,ℝ))) Y where
  ell θ := d.ell (pathHeatNativeSourceRestrictionState ι θ)
  phi θ := d.phi (pathHeatNativeSourceRestrictionState ι θ)
  dotell θ := d.dotell (pathHeatNativeSourceRestrictionState ι θ)
  dotphi θ := d.dotphi (pathHeatNativeSourceRestrictionState ι θ)
  S θ := (d.S (pathHeatNativeSourceRestrictionState ι θ)).map ι
  P θ := (d.P (pathHeatNativeSourceRestrictionState ι θ)).map ι
  M θ := (d.M (pathHeatNativeSourceRestrictionState ι θ)).map (pathHeatIndexPairMap ι)
  Q θ := (d.Q (pathHeatNativeSourceRestrictionState ι θ)).map (pathHeatIndexPairMap ι)
  B := d.B
  Ds := d.Ds
  Dm := d.Dm
  Dp := d.Dp
  Dq := d.Dq
  Dt := d.Dt
  Dphi := d.Dphi
  continuous_ell := d.continuous_ell.comp (continuous_pathHeatNativeSourceRestrictionState ι)
  continuous_phi := d.continuous_phi.comp (continuous_pathHeatNativeSourceRestrictionState ι)
  continuous_dotell := d.continuous_dotell.comp (continuous_pathHeatNativeSourceRestrictionState ι)
  continuous_dotphi := d.continuous_dotphi.comp (continuous_pathHeatNativeSourceRestrictionState ι)
  continuous_S θ := tendsto_pathHeatIndexPushforward_tv_sub (𝓝 θ) ι
    (fun v=>d.S (pathHeatNativeSourceRestrictionState ι v))
    (d.S (pathHeatNativeSourceRestrictionState ι θ))
    ((d.continuous_S _).comp (continuous_pathHeatNativeSourceRestrictionState ι).continuousAt.tendsto)
  continuous_P θ := tendsto_pathHeatIndexPushforward_tv_sub (𝓝 θ) ι
    (fun v=>d.P (pathHeatNativeSourceRestrictionState ι v))
    (d.P (pathHeatNativeSourceRestrictionState ι θ))
    ((d.continuous_P _).comp (continuous_pathHeatNativeSourceRestrictionState ι).continuousAt.tendsto)
  continuous_M θ := tendsto_pathHeatIndexPushforward_tv_sub (𝓝 θ) (pathHeatIndexPairMap ι)
    (fun v=>d.M (pathHeatNativeSourceRestrictionState ι v))
    (d.M (pathHeatNativeSourceRestrictionState ι θ))
    ((d.continuous_M _).comp (continuous_pathHeatNativeSourceRestrictionState ι).continuousAt.tendsto)
  continuous_Q θ := tendsto_pathHeatIndexPushforward_tv_sub (𝓝 θ) (pathHeatIndexPairMap ι)
    (fun v=>d.Q (pathHeatNativeSourceRestrictionState ι v))
    (d.Q (pathHeatNativeSourceRestrictionState ι θ))
    ((d.continuous_Q _).comp (continuous_pathHeatNativeSourceRestrictionState ι).continuousAt.tendsto)
  bound_phi θ := d.bound_phi _
  bound_dotell θ := d.bound_dotell _
  bound_dotphi θ := d.bound_dotphi _
  bound_S θ := (pathHeatIndexPushforward_tv_le ι _).trans (d.bound_S _)
  bound_P θ := (pathHeatIndexPushforward_tv_le ι _).trans (d.bound_P _)
  bound_M θ := (pathHeatIndexPushforward_tv_le (pathHeatIndexPairMap ι) _).trans (d.bound_M _)
  bound_Q θ := (pathHeatIndexPushforward_tv_le (pathHeatIndexPairMap ι) _).trans (d.bound_Q _)

structure PathHeatNativeAnalyticSource (a b : ℝ) (hab : a≤b)
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(X,ℝ))) X) (C : ℝ≥0) : Prop where
  ell_derivative : ∀z ω p,HasFDerivAt (fun q=>d.ell (z,(ω,q)))
    (pathHeatSignedScore (d.S (z,(ω,p)))) p
  phi_derivative : ∀z ω p,HasFDerivAt (fun q=>d.phi (z,(ω,q)))
    (pathHeatSignedScore (d.P (z,(ω,p)))) p
  score_derivative : ∀z ω p,HasFDerivAt (fun q=>pathHeatSignedScore (d.S (z,(ω,q))))
    (pathHeatSignedHessian (d.M (z,(ω,p)))) p
  phi_score_derivative : ∀z ω p,HasFDerivAt (fun q=>pathHeatSignedScore (d.P (z,(ω,q))))
    (pathHeatSignedHessian (d.Q (z,(ω,p)))) p
  ell_parameter : ∀ω z,z∈Ioo a b→∀p,
    HasDerivAt (fun u=>d.ell (projIcc a b hab u,(ω,p)))
      (d.dotell (projIcc a b hab z,(ω,p))) z
  phi_parameter : ∀ω z,z∈Ioo a b→∀p,
    HasDerivAt (fun u=>d.phi (projIcc a b hab u,(ω,p)))
      (d.dotphi (projIcc a b hab z,(ω,p))) z
  ell_growth : ∀z ω p,|d.ell (z,(ω,p))|≤C*(1+‖ω.1‖+‖p‖)

theorem pathHeatNativeSourceExtension_wiener_analytic {L : ℕ}
    (hab : a≤b) (ι : C(X,Fin L×I))
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(X,ℝ))) X)
    (C : ℝ≥0) (h : PathHeatNativeAnalyticSource a b hab d C) :
    PathHeatWienerAnalyticSource a b hab (pathHeatNativeSourceExtension ι d) C := by
  constructor
  · intro z ω p
    change HasFDerivAt (fun q=>d.ell (z,(ω,pathHeatIndexRestriction ι q)))
      (pathHeatSignedScore ((d.S (z,(ω,pathHeatIndexRestriction ι p))).map ι)) p
    exact hasFDerivAt_pathHeatIndexExtension ι _ _ p (h.ell_derivative z ω _)
  · intro z ω p
    change HasFDerivAt (fun q=>d.phi (z,(ω,pathHeatIndexRestriction ι q)))
      (pathHeatSignedScore ((d.P (z,(ω,pathHeatIndexRestriction ι p))).map ι)) p
    exact hasFDerivAt_pathHeatIndexExtension ι _ _ p (h.phi_derivative z ω _)
  · intro z ω p
    change HasFDerivAt (fun q=>pathHeatSignedScore ((d.S (z,(ω,pathHeatIndexRestriction ι q))).map ι))
      (pathHeatSignedHessian ((d.M (z,(ω,pathHeatIndexRestriction ι p))).map (pathHeatIndexPairMap ι))) p
    exact hasFDerivAt_pathHeatIndexExtensionScore ι (fun q=>d.S (z,(ω,q)))
      (fun q=>d.M (z,(ω,q))) (h.score_derivative z ω) p
  · intro z ω p
    change HasFDerivAt (fun q=>pathHeatSignedScore ((d.P (z,(ω,pathHeatIndexRestriction ι q))).map ι))
      (pathHeatSignedHessian ((d.Q (z,(ω,pathHeatIndexRestriction ι p))).map (pathHeatIndexPairMap ι))) p
    exact hasFDerivAt_pathHeatIndexExtensionScore ι (fun q=>d.P (z,(ω,q)))
      (fun q=>d.Q (z,(ω,q))) (h.phi_score_derivative z ω) p
  · intro ω z hz p
    exact h.ell_parameter ω z hz (pathHeatIndexRestriction ι p)
  · intro ω z hz p
    exact h.phi_parameter ω z hz (pathHeatIndexRestriction ι p)
  · intro z ω p
    exact (h.ell_growth z ω (pathHeatIndexRestriction ι p)).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (pathHeatIndexRestriction_norm_apply_le ι p))
        C.coe_nonneg)

def pathHeatFiniteTreeSourceExtension (A J : ℕ)
    (d : PathHeatContinuousSignedSource
      (Icc a b×((E×K)×C(pathHeatFiniteTreeIndex A J,ℝ))) (pathHeatFiniteTreeIndex A J)) :
    PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin (A+J)×I,ℝ))) (Fin (A+J)×I) :=
  pathHeatNativeSourceExtension (pathHeatFiniteTreeIndexEmbedding A J) d

theorem pathHeatFiniteTreeSourceExtension_analytic (A J : ℕ) (hab : a≤b)
    (d : PathHeatContinuousSignedSource
      (Icc a b×((E×K)×C(pathHeatFiniteTreeIndex A J,ℝ))) (pathHeatFiniteTreeIndex A J))
    (C : ℝ≥0) (h : PathHeatNativeAnalyticSource a b hab d C) :
    PathHeatWienerAnalyticSource a b hab (pathHeatFiniteTreeSourceExtension A J d) C :=
  pathHeatNativeSourceExtension_wiener_analytic hab (pathHeatFiniteTreeIndexEmbedding A J) d C h

end HexagonPaper
