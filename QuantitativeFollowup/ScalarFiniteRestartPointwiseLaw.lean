module
public import FourPapersCommon.MixedFiniteRestartKernelAE
public import FourPapersCommon.MixedFiniteEndpointFeller
public import FourPapersCommon.QuadraticMixture
public import QuantitativeFollowup.ScalarFutureContinuity

@[expose] public section

/-! Every finite normalized Gaussian endpoint transition is the actual
fresh restarted scalar diffusion, for every initial field. Coincident
nodes and a zero starting node are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper FourPapersCommon
open SpinGlass SpinGlass.Targets
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem continuous_scalarTransitionExpectation_bounded (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ)≤q) (F : ℝ→ℝ) (hF : Continuous F)
    (C : ℝ) (hb : ∀x,‖F x‖≤C) :
    Continuous (scalarTransitionExpectation β μ r q hrq F) := by
  have he (x : ℝ) : scalarTransitionExpectation β μ r q hrq F x=
      ∫W,F (scalarFutureEndpointExtended β μ r q x W) ∂canonicalWienerMeasure := by
    simp only [scalarTransitionExpectation,scalarFutureEndpointExtended_eq β μ r q hrq]
  change Continuous (fun x=>scalarTransitionExpectation β μ r q hrq F x)
  simp_rw [he]
  apply continuous_of_dominated (μ:=canonicalWienerMeasure) (bound:=fun _=>C)
  · intro x
    have harg : Continuous (fun W : C(Paper.Overlap,ℝ)=>((μ,(r,(q,x))),W)):=by fun_prop
    have hc : Continuous (fun W : C(Paper.Overlap,ℝ)=>F (scalarFutureEndpointExtended β μ r q x W)) := by
      simpa only [Function.comp_def] using hF.comp ((continuous_scalarFutureEndpointExtended β).comp harg)
    exact hc.aestronglyMeasurable
  · intro x
    exact .of_forall fun W=>hb _
  · exact integrable_const C
  · apply Filter.Eventually.of_forall
    intro W
    have harg : Continuous (fun x : ℝ=>((μ,(r,(q,x))),W)):=by fun_prop
    simpa only [Function.comp_def] using hF.comp ((continuous_scalarFutureEndpointExtended β).comp harg)

theorem integral_parisiPhysicalRestartKernel (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ)≤q)
    (F : ℝ→ℝ) (hF : Measurable F) (x : ℝ) :
    (∫y,F y ∂parisiPhysicalRestartKernel β μ r q hrq x)=
      scalarTransitionExpectation β μ r q hrq F x := by
  rw [parisiPhysicalRestartKernel,independentNoiseKernel_apply _ _
    (measurable_parisiPhysicalRestartEndpoint β hβ μ r q hrq)]
  exact integral_map ((measurable_parisiPhysicalRestartEndpoint β hβ μ r q hrq).comp
    measurable_prodMk_left).aemeasurable hF.aestronglyMeasurable

theorem scalarSchemeEndpoint_eq_restart_bounded_integral {k : ℕ}
    (s : RSBScheme k) (β : ℝ) (hβ : 0<β) (p n : ℕ) (hn : p+n≤k+2)
    (r q : Paper.Overlap) (hr : (r : ℝ)=s.q p) (hq : (q : ℝ)=s.q (p+n))
    (hrq : (r : ℝ)≤q) (F : ℝ→ℝ) (hF : Continuous F)
    (C : ℝ) (hb : ∀x,‖F x‖≤C) (x : ℝ) :
    (∫y,F y ∂mixedSchemeEndpointKernel
      (AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)) s p n x)=
      scalarTransitionExpectation β (Paper.parisiSchemeMeasure s) r q hrq F x := by
  let ξ:=AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)
  let μ:=Paper.parisiSchemeMeasure s
  let J:=mixedSchemeEndpointKernel ξ s p n
  let K:=parisiPhysicalRestartKernel β μ r q hrq
  have hbeta : mixedBeta ξ=β:=by simp only [ξ,mixedBeta_quadratic,Real.sqrt_sq_eq_abs,abs_of_pos hβ]
  have hm : mixedMeasure ξ μ=μ:=mixedMeasure_quadratic _ _ _
  have hc : ξ.unitClock=id:=AdmissibleEvenMixture.quadratic_unitClock _ _
  have hae (h : ℝ) : K=ᵐ[Paper.canonicalBrownianMeasure.map
      (fun ω=>mixedState ξ h μ ω r)] J := by
    have he:=mixedSchemeEndpointKernel_eq_restart_ae ξ h s p n hn r q hr hq
    simpa only [hbeta,hm,hc,id_eq,K,J,μ] using he
  have hK (y : ℝ) : (∫z,F z ∂K y)=scalarTransitionExpectation β μ r q hrq F y :=
    integral_parisiPhysicalRestartKernel β hβ.ne' μ r q hrq F hF.measurable y
  rcases eq_or_lt_of_le r.property.1 with hz | hpos
  · have hz0 : (r : ℝ)=0:=hz.symm
    have ha:=hae x
    have hstate : (fun ω=>mixedState ξ x μ ω r)=(fun _ : Paper.BrownianSample=>x) := by
      funext ω
      rw [hz0,mixedState_initial]
    rw [hstate] at ha
    have he : K x=J x:=by
      change ∀ᶠy in ae (Paper.canonicalBrownianMeasure.map (fun _=>x)),K y=J y at ha
      simpa only [Measure.map_const,measure_univ,one_smul,ae_dirac_eq,eventually_pure] using ha
    rw [←he,hK]
  · letI : Measure.IsOpenPosMeasure (Paper.canonicalBrownianMeasure.map
        (fun ω=>mixedState ξ 0 μ ω r)) := by
      have he:=mixedFiniteNodeLaw_isOpenPos ξ 0 s p (by omega) (by rwa [←hr])
      simpa only [μ,←hr] using he
    have he : (fun y=>∫z,F z ∂J y)=ᵐ[Paper.canonicalBrownianMeasure.map
        (fun ω=>mixedState ξ 0 μ ω r)] scalarTransitionExpectation β μ r q hrq F := by
      filter_upwards [hae 0] with y hy
      rw [←hy,hK]
    have hh:=Measure.eq_of_ae_eq he
      (continuous_mixedSchemeEndpoint_bounded_integral ξ s p n hn F hF C hb)
      (continuous_scalarTransitionExpectation_bounded β μ r q hrq F hF C hb)
    exact congrFun hh x

theorem scalarSchemeEndpoint_eq_futureSquare {k : ℕ}
    (s : RSBScheme k) (β : ℝ) (hβ : 0<β) (p n : ℕ) (hn : p+n≤k+2)
    (r q : Paper.Overlap) (hr : (r : ℝ)=s.q p) (hq : (q : ℝ)=s.q (p+n))
    (hrq : (r : ℝ)≤q) (x : ℝ) :
    (∫y,Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (q,y)^2
      ∂mixedSchemeEndpointKernel (AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)) s p n x)=
      scalarFutureSquare β (Paper.parisiSchemeMeasure s) r q hrq x := by
  apply scalarSchemeEndpoint_eq_restart_bounded_integral s β hβ p n hn r q hr hq hrq
    (fun y=>Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (q,y)^2)
    (((Paper.continuous_parisiGradient β _).comp (continuous_const.prodMk continuous_id)).pow 2) 1
  intro y
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_parisiGradient_le_one β _ _) 

end QuantitativeFollowup
