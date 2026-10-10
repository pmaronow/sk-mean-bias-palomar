module
public import HexagonPaper.PathHeatSectionwiseAnalyticSource
public import HexagonPaper.PathHeatNativeGeneratorTransfer
public import HexagonPaper.PathHeatTreeBernsteinFiniteCoordinatesJets

@[expose] public section

/-! Native-index extension of sectionwise-continuous signed jets.
The pushforward construction preserves the precise auxiliary regularity. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval NNReal BoundedContinuousFunction
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

theorem pathHeatSectionwise_index_tv {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (ι : C(X,Y)) (ν : A→SignedMeasure X)
    (hν : ∀v,Tendsto (fun w=>signedTV (ν w-ν v)) (𝓝 v) (𝓝 0))
    (f : B→A) (hf : Continuous f) (v : B) :
    Tendsto (fun w=>signedTV ((ν (f w)).map ι-(ν (f v)).map ι)) (𝓝 v) (𝓝 0) :=
  tendsto_pathHeatIndexPushforward_tv_sub (𝓝 v) ι
    (fun w=>ν (f w)) (ν (f v)) ((hν (f v)).comp hf.continuousAt.tendsto)

def pathHeatSectionwiseNativeSourceExtension (ι : C(X,Y))
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X) :
    PathHeatSectionwiseSignedSource (Icc a b) E K Y where
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
  continuous_S (aux : E×K) (v : Icc a b×C(Y,ℝ)) := pathHeatSectionwise_index_tv ι
    (fun u : Icc a b×C(X,ℝ)=>d.S (u.1,(aux,u.2))) (d.continuous_S aux)
    (fun w : Icc a b×C(Y,ℝ)=>(w.1,pathHeatIndexRestriction ι w.2))
    (continuous_fst.prodMk ((pathHeatIndexRestriction ι).continuous.comp continuous_snd)) v
  continuous_P (aux : E×K) (v : Icc a b×C(Y,ℝ)) := pathHeatSectionwise_index_tv ι
    (fun u : Icc a b×C(X,ℝ)=>d.P (u.1,(aux,u.2))) (d.continuous_P aux)
    (fun w : Icc a b×C(Y,ℝ)=>(w.1,pathHeatIndexRestriction ι w.2))
    (continuous_fst.prodMk ((pathHeatIndexRestriction ι).continuous.comp continuous_snd)) v
  continuous_M (aux : E×K) (v : Icc a b×C(Y,ℝ)) := pathHeatSectionwise_index_tv (pathHeatIndexPairMap ι)
    (fun u : Icc a b×C(X,ℝ)=>d.M (u.1,(aux,u.2))) (d.continuous_M aux)
    (fun w : Icc a b×C(Y,ℝ)=>(w.1,pathHeatIndexRestriction ι w.2))
    (continuous_fst.prodMk ((pathHeatIndexRestriction ι).continuous.comp continuous_snd)) v
  continuous_Q (aux : E×K) (v : Icc a b×C(Y,ℝ)) := pathHeatSectionwise_index_tv (pathHeatIndexPairMap ι)
    (fun u : Icc a b×C(X,ℝ)=>d.Q (u.1,(aux,u.2))) (d.continuous_Q aux)
    (fun w : Icc a b×C(Y,ℝ)=>(w.1,pathHeatIndexRestriction ι w.2))
    (continuous_fst.prodMk ((pathHeatIndexRestriction ι).continuous.comp continuous_snd)) v
  bound_phi θ := d.bound_phi _
  bound_dotell θ := d.bound_dotell _
  bound_dotphi θ := d.bound_dotphi _
  bound_S θ := (pathHeatIndexPushforward_tv_le ι _).trans (d.bound_S _)
  bound_P θ := (pathHeatIndexPushforward_tv_le ι _).trans (d.bound_P _)
  bound_M θ := (pathHeatIndexPushforward_tv_le (pathHeatIndexPairMap ι) _).trans (d.bound_M _)
  bound_Q θ := (pathHeatIndexPushforward_tv_le (pathHeatIndexPairMap ι) _).trans (d.bound_Q _)

theorem pathHeatSectionwiseNativeSourceExtension_analytic {L : ℕ}
    (hab : a≤b) (ι : C(X,Fin L×I))
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (C : ℝ≥0) (h : PathHeatSectionwiseAnalyticSource a b hab d C) :
    PathHeatSectionwiseAnalyticSource a b hab (pathHeatSectionwiseNativeSourceExtension ι d) C := by
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


theorem pathHeatSectionwiseNativeSourceExtension_densityGenerator (ι : C(X,Y))
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (kernel : Y×Y→ᵇℝ) (θ : Icc a b×((E×K)×C(Y,ℝ))) :
    (pathHeatSectionwiseNativeSourceExtension ι d).densityGenerator kernel θ=
      d.densityGenerator (pathHeatNativeKernelRestriction ι kernel)
        (pathHeatNativeSourceRestrictionState ι θ) :=
  pathHeatDensityGenerator_indexPushforward ι kernel _ _ _

theorem pathHeatSectionwiseNativeSourceExtension_observableGenerator (ι : C(X,Y))
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (kernel : Y×Y→ᵇℝ) (θ : Icc a b×((E×K)×C(Y,ℝ))) :
    (pathHeatSectionwiseNativeSourceExtension ι d).observableGenerator kernel θ=
      d.observableGenerator (pathHeatNativeKernelRestriction ι kernel)
        (pathHeatNativeSourceRestrictionState ι θ) :=
  pathHeatObservableGenerator_indexPushforward ι kernel _ _ _ _


theorem pathHeatSectionwiseNativeSourceExtension_densityGenerator_continuousKernel (ι : C(X,Y))
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (kernel : C(Y×Y,ℝ)) (θ : Icc a b×((E×K)×C(Y,ℝ))) :
    (pathHeatSectionwiseNativeSourceExtension ι d).densityGenerator (BoundedContinuousFunction.mkOfCompact kernel) θ=
      d.densityGenerator (BoundedContinuousFunction.mkOfCompact (kernel.comp (pathHeatIndexPairMap ι)))
        (pathHeatNativeSourceRestrictionState ι θ) :=
  pathHeatSectionwiseNativeSourceExtension_densityGenerator ι d _ θ

theorem pathHeatSectionwiseNativeSourceExtension_observableGenerator_continuousKernel (ι : C(X,Y))
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (kernel : C(Y×Y,ℝ)) (θ : Icc a b×((E×K)×C(Y,ℝ))) :
    (pathHeatSectionwiseNativeSourceExtension ι d).observableGenerator (BoundedContinuousFunction.mkOfCompact kernel) θ=
      d.observableGenerator (BoundedContinuousFunction.mkOfCompact (kernel.comp (pathHeatIndexPairMap ι)))
        (pathHeatNativeSourceRestrictionState ι θ) :=
  pathHeatSectionwiseNativeSourceExtension_observableGenerator ι d _ θ


end HexagonPaper
