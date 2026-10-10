module
public import HexagonPaper.PathHeatWienerFiniteLaw
public import HexagonPaper.PathHeatWienerFiniteGenerators
public import HexagonPaper.PathHeatWienerAnalyticSource

@[expose] public section

/-! Actual conditional finite Price differentiation on the canonical
Wiener reference. Auxiliary Gaussian/counting coordinates are fixed here;
the raw numerator and normalizer are differentiated separately. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal BoundedContinuousFunction
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L n : ℕ} {a b : ℝ}

theorem bernstein_z_strictMono (n : ℕ) (hn : n≠0) : StrictMono (@bernstein.z n) := by
  intro i j hij
  change (i:ℝ)/(n:ℝ)<(j:ℝ)/(n:ℝ)
  exact (div_lt_div_iff_of_pos_right (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr (by exact_mod_cast hij)

theorem pathHeatWiener_mesh_variance_pos
    (c : ℝ→Fin L→C(I,I)) (n : ℕ) (hn : n≠0) (z : ℝ)
    (hc : ∀l,StrictMono (c z l)) (α : Fin (L*n)) :
    0<pathHeatBrownianClockVariance (pathHeatClockMesh n c) z α := by
  unfold pathHeatBrownianClockVariance pathHeatClockMesh
  apply sub_pos.mpr
  exact hc _ (bernstein_z_strictMono n hn (by
    simp only [Fin.lt_def,Fin.val_castSucc,Fin.val_succ]
    omega))

def pathHeatWienerFiniteConditionalState (hab : a≤b)
    (c : ℝ→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (aux : E×K) (z : ℝ) (w : Fin L→WienerPath) :
    Icc a b×((E×K)×C(Fin L×I,ℝ)) :=
  (projIcc a b hab z,(aux,pathHeatTreeMixedOperator δ W
    (pathHeatTreeBernsteinOperator n L (pathHeatFlatClockPath L (c z) w))))

def pathHeatWienerFiniteConditionalNormalizer (hab : a≤b)
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin L×I,ℝ))) (Fin L×I))
    (c : ℝ→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (aux : E×K) (z : ℝ) : ℝ :=
  ∫w,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)
    ∂pathHeatWienerMeshBase (J:=Fin L)

def pathHeatWienerFiniteConditionalNumerator (hab : a≤b)
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin L×I,ℝ))) (Fin L×I))
    (c : ℝ→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (aux : E×K) (z : ℝ) : ℝ :=
  ∫w,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)*
    d.phi (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)
    ∂pathHeatWienerMeshBase (J:=Fin L)

def pathHeatWienerFiniteConditionalNormalizerDerivative (hab : a≤b)
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin L×I,ℝ))) (Fin L×I))
    (c : ℝ→Fin L→C(I,I)) (dc : ℝ→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (aux : E×K) (z : ℝ) : ℝ :=
  ∫w,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)*
    d.densityGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
      (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)
    ∂pathHeatWienerMeshBase (J:=Fin L)

def pathHeatWienerFiniteConditionalNumeratorDerivative (hab : a≤b)
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin L×I,ℝ))) (Fin L×I))
    (c : ℝ→Fin L→C(I,I)) (dc : ℝ→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (aux : E×K) (z : ℝ) : ℝ :=
  ∫w,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)*
    (d.observableGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
      (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)+
      d.phi (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)*
        d.densityGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
          (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w))
    ∂pathHeatWienerMeshBase (J:=Fin L)

theorem pathHeatWiener_finite_conditional_derivatives
    (hab : a≤b) (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin L×I,ℝ))) (Fin L×I))
    (C : ℝ≥0) (hsource : PathHeatWienerAnalyticSource a b hab d C)
    (c : ℝ→Fin L→C(I,I)) (dc : ℝ→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (hn : n≠0)
    (hc : ∀z∈Ioo a b,∀l,StrictMono (c z l))
    (hroot : ∀z l,c z l 0=0)
    (hdc : ∀z∈Ioo a b,∀l t,HasDerivAt (fun u=>(c u l t:ℝ)) (dc z l t) z)
    (hdcc : ∀z∈Ioo a b,∀l,ContinuousAt (fun u=>dc u l) z)
    (aux : E×K) (z : ℝ) (hz : z∈Ioo a b) :
    0<pathHeatWienerFiniteConditionalNormalizer (n:=n) hab d c δ W aux z ∧
    HasDerivAt (pathHeatWienerFiniteConditionalNormalizer (n:=n) hab d c δ W aux)
      (pathHeatWienerFiniteConditionalNormalizerDerivative (n:=n) hab d c dc δ W aux z) z ∧
    HasDerivAt (pathHeatWienerFiniteConditionalNumerator (n:=n) hab d c δ W aux)
      (pathHeatWienerFiniteConditionalNumeratorDerivative (n:=n) hab d c dc δ W aux z) z := by
  let A := pathHeatTreeMixedFlattenedSynthesis n L δ W
  let ell := pathHeatWienerRealFamily a b hab d.ell aux
  let Phi := pathHeatWienerRealFamily a b hab d.phi aux
  let dotell := pathHeatWienerRealJoint a b hab d.dotell aux
  let dotPhi := pathHeatWienerRealJoint a b hab d.dotphi aux
  let S := pathHeatWienerRealJoint a b hab d.S aux
  let P := pathHeatWienerRealJoint a b hab d.P aux
  let M := pathHeatWienerRealJoint a b hab d.M aux
  let Q := pathHeatWienerRealJoint a b hab d.Q aux
  let v := pathHeatBrownianClockVariance (pathHeatClockMesh n c)
  let dv := pathHeatClockMeshDerivative n dc
  have hmesh : pathHeatWienerBernsteinClockMesh (n:=n) c=pathHeatClockMesh n c := rfl
  have hpars := pathHeatWiener_source_parameter_data hab d C hsource aux
  have hdvc (α : Fin (L*n)) : ContinuousAt (fun u=>dv u α) z := by
    unfold dv pathHeatClockMeshDerivative
    exact ((continuous_eval_const _).continuousAt.comp (hdcc z hz _)).sub
      ((continuous_eval_const _).continuousAt.comp (hdcc z hz _))
  have hr := pathHeat_signed_source_finite_generator_response a b hab z hz A ell Phi dotell dotPhi S P M Q
    d.B d.Ds d.Dm d.Dp d.Dq (pathHeatWienerAuxGrowthConstant C aux) C d.Dt d.Dphi
    (pathHeatWiener_source_spatial_bounds hab d C hsource aux) hpars.1 hpars.2
    (fun u _ p=>d.bound_dotell _) (fun u _ p=>d.bound_dotphi _)
    v dv pathHeatBrownianClockMask
    (fun u hu=>pathHeatWiener_mesh_variance_pos c n hn u (hc u hu))
    (fun u hu=>pathHeatClockMeshVariance_hasDerivAt n c dc u (hdc u hu)) hdvc 0
  have h0 := pathHeatClockDerivative_root_zero c dc z (hdc z hz) hroot
  have hmono (u : ℝ) (hu : u∈Ioo a b) (l : Fin L) :
      Monotone (pathHeatWienerBernsteinClockMesh (n:=n) c u l) :=
    (hc u hu l).monotone.comp (bernstein_z_monotone n)
  have hzero (u : ℝ) (l : Fin L) : (pathHeatWienerBernsteinClockMesh (n:=n) c u l 0:ℝ)=0 := by
    simp only [pathHeatWienerBernsteinClockMesh,bernstein.z_zero,hroot]
    rfl
  have fib (u : ℝ) : Continuous (fun p : C(Fin L×I,ℝ)=>(projIcc a b hab u,(aux,p))) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have hZeq (u : ℝ) (hu : u∈Ioo a b) :
      pathHeatWienerFiniteConditionalNormalizer (n:=n) hab d c δ W aux u=
        pathHeatSourceFiniteNormalizer A ell v pathHeatBrownianClockMask 0 u := by
    simpa only [pathHeatWienerFiniteConditionalNormalizer,pathHeatWienerFiniteConditionalState,
      pathHeatSourceFiniteNormalizer,PathHeatContinuousSignedSource.weight,ell,v,A,pathHeatWienerRealFamily,
      hmesh,pathHeatWienerBernsteinClockMesh,pathHeatClockMesh] using
      integral_pathHeatWienerMixedBernstein_eq_gaussian c δ W u (hmono u hu) (hzero u)
        (fun p=>d.weight (projIcc a b hab u,(aux,p))) (d.continuous_weight.measurable.comp (fib u).measurable)
  have hNeq (u : ℝ) (hu : u∈Ioo a b) :
      pathHeatWienerFiniteConditionalNumerator (n:=n) hab d c δ W aux u=
        pathHeatSourceFiniteNumerator A ell Phi v pathHeatBrownianClockMask 0 u := by
    simpa only [pathHeatWienerFiniteConditionalNumerator,pathHeatWienerFiniteConditionalState,
      pathHeatSourceFiniteNumerator,PathHeatContinuousSignedSource.weight,ell,Phi,v,A,pathHeatWienerRealFamily,
      hmesh,pathHeatWienerBernsteinClockMesh,pathHeatClockMesh] using
      integral_pathHeatWienerMixedBernstein_eq_gaussian c δ W u (hmono u hu) (hzero u)
        (fun p=>d.weight (projIcc a b hab u,(aux,p))*d.phi (projIcc a b hab u,(aux,p)))
          ((d.continuous_weight.mul d.continuous_phi).measurable.comp (fib u).measurable)
  have hHZ (y : QuantitativePaper.Field (L*(n+1))) := pathHeatWienerFinite_density_generator δ W dc dotell S M z h0 y
  have hJN (y : QuantitativePaper.Field (L*(n+1))) := pathHeatWienerFinite_observable_generator δ W dc dotPhi S P Q z h0 y
  have hZD : pathHeatWienerFiniteConditionalNormalizerDerivative (n:=n) hab d c dc δ W aux z=
      (∫g,Real.exp (ell z (A (pathHeatVarianceFactor v pathHeatBrownianClockMask z g)))*
        pathHeatSourceFiniteDensityGenerator A dotell S M dv pathHeatBrownianClockMask z
          (pathHeatVarianceFactor v pathHeatBrownianClockMask z g) ∂fieldGaussian (L*n)) := by
    have hi := integral_pathHeatWienerMixedBernstein_eq_gaussian c δ W z (hmono z hz) (hzero z)
      (fun p=>d.weight (projIcc a b hab z,(aux,p))*
        d.densityGenerator (pathHeatWienerFiniteKernel n L δ W dc z) (projIcc a b hab z,(aux,p)))
      ((d.continuous_weight.mul (d.continuous_densityGenerator _)).measurable.comp (fib z).measurable)
    simpa only [pathHeatWienerFiniteConditionalNormalizerDerivative,pathHeatWienerFiniteConditionalState,
      gaussianLinearMean,zero_add,hHZ,A,ell,dotell,S,M,v,dv,
      pathHeatWienerRealFamily,pathHeatWienerRealJoint,hmesh,pathHeatWienerBernsteinClockMesh,pathHeatClockMesh,
      PathHeatContinuousSignedSource.weight,PathHeatContinuousSignedSource.densityGenerator] using hi
  have hND : pathHeatWienerFiniteConditionalNumeratorDerivative (n:=n) hab d c dc δ W aux z=
      (∫g,Real.exp (ell z (A (pathHeatVarianceFactor v pathHeatBrownianClockMask z g)))*
        (pathHeatSourceFiniteObservableGenerator A dotPhi S P Q dv pathHeatBrownianClockMask z
          (pathHeatVarianceFactor v pathHeatBrownianClockMask z g)+
          Phi z (A (pathHeatVarianceFactor v pathHeatBrownianClockMask z g))*
            pathHeatSourceFiniteDensityGenerator A dotell S M dv pathHeatBrownianClockMask z
              (pathHeatVarianceFactor v pathHeatBrownianClockMask z g)) ∂fieldGaussian (L*n)) := by
    have hi := integral_pathHeatWienerMixedBernstein_eq_gaussian c δ W z (hmono z hz) (hzero z)
      (fun p=>d.weight (projIcc a b hab z,(aux,p))*
        (d.observableGenerator (pathHeatWienerFiniteKernel n L δ W dc z) (projIcc a b hab z,(aux,p))+
          d.phi (projIcc a b hab z,(aux,p))*
            d.densityGenerator (pathHeatWienerFiniteKernel n L δ W dc z) (projIcc a b hab z,(aux,p))))
      ((d.continuous_weight.mul ((d.continuous_observableGenerator _).add
        (d.continuous_phi.mul (d.continuous_densityGenerator _)))).measurable.comp (fib z).measurable)
    simpa only [pathHeatWienerFiniteConditionalNumeratorDerivative,pathHeatWienerFiniteConditionalState,
      gaussianLinearMean,zero_add,hHZ,hJN,A,ell,Phi,dotell,dotPhi,S,P,M,Q,v,dv,
      pathHeatWienerRealFamily,pathHeatWienerRealJoint,hmesh,pathHeatWienerBernsteinClockMesh,pathHeatClockMesh,
      PathHeatContinuousSignedSource.weight,PathHeatContinuousSignedSource.densityGenerator,
      PathHeatContinuousSignedSource.observableGenerator] using hi
  refine ⟨by rw [hZeq z hz];exact hr.1,?_,?_⟩
  · have he : pathHeatWienerFiniteConditionalNormalizer (n:=n) hab d c δ W aux =ᶠ[𝓝 z]
        pathHeatSourceFiniteNormalizer A ell v pathHeatBrownianClockMask 0 := by
      filter_upwards [isOpen_Ioo.mem_nhds hz] with u hu
      exact hZeq u hu
    simpa only [zero_add,hZD] using (hr.2.1.congr_of_eventuallyEq he)
  · have he : pathHeatWienerFiniteConditionalNumerator (n:=n) hab d c δ W aux =ᶠ[𝓝 z]
        pathHeatSourceFiniteNumerator A ell Phi v pathHeatBrownianClockMask 0 := by
      filter_upwards [isOpen_Ioo.mem_nhds hz] with u hu
      exact hNeq u hu
    simpa only [zero_add,hND] using (hr.2.2.1.congr_of_eventuallyEq he)

end HexagonPaper
