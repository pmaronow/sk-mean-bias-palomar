module
public import QuantitativeFollowup.ScalarTransportSpatialContinuity
public import QuantitativeFollowup.ScalarTransportGaussianLocalBounds
public import QuantitativeFollowup.ParameterJointDerivatives
public import QuantitativeFollowup.FiniteMarkedGaussianResponse

@[expose] public section

/-! Normalized Gaussian response of the actual scalar transport family from
genuine bounded continuous parameter partials. This is an analytic intermediate:
the parameter-partial hypotheses must be discharged by the physical moved-node
variation. The target physical moment and all normalization, spatial data,
Gaussian input curves and integration bounds are already actual and proved. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators ContDiff
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem hasDerivAt_scalarTransportGamma_of_actual_partials
    (s : RSBScheme k) (β : ℝ) (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (p : Fin (k+3))
    (DV : Bool→ℝ→QuantitativePaper.Field (k+3)→ℝ)
    (DF : ℝ→QuantitativePaper.Field (k+3)→ℝ)
    (hDV : ∀e,∀u∈Ioo (-δ) δ,∀x,HasDerivAt
      (fun v=>scalarTransportEuclideanExponent s β φ e v x) (DV e u x) u)
    (hDF : ∀u∈Ioo (-δ) δ,∀x,HasDerivAt
      (fun v=>scalarTransportGradientSquare s β φ p v x) (DF u x) u)
    (hcDV : ∀e,ContinuousOn (Function.uncurry (DV e)) (Ioo (-δ) δ ×ˢuniv))
    (hcDF : ContinuousOn (Function.uncurry DF) (Ioo (-δ) δ ×ˢuniv))
    (P Q : ℝ) (hP : 0≤P) (hQ : 0≤Q)
    (hbDV : ∀e,∀u∈Ioo (-δ) δ,∀x,‖DV e u x‖≤P)
    (hbDF : ∀u∈Ioo (-δ) δ,∀x,‖DF u x‖≤Q) :
    HasDerivAt (fun u=>FRSB.Gamma β (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
      (scalarLevelTransport φ u (scalarSchemeTransportNode s p)))
      ((1/2:ℝ)*∑e : Bool,∫z,Real.exp (scalarTransportEuclideanExponent s β φ e 0
          (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ 0) (k+2) z))*(
        DF 0 (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ 0) (k+2) z)+
        (scalarTransportGradientSquare s β φ p 0
          (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ 0) (k+2) z)-
          FRSB.Gamma β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p))*
            DV e 0 (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ 0) (k+2) z)+
        ∑i : Fin (k+2),gaussianScoreBilinear (scalarTransportEuclideanExponent s β φ e 0)
          (scalarTransportGradientSquare s β φ p 0)
          (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ 0) (k+2) z)
          (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ 0) (k+2) (EuclideanSpace.single i 1))
          (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficientDerivative s β φ 0) (k+2) (EuclideanSpace.single i 1))
          (FRSB.Gamma β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p))) ∂fieldGaussian (k+2)) 0 := by
  let S := Ioo (-δ) δ
  have hS : S∈𝓝 (0:ℝ) := isOpen_Ioo.mem_nhds ⟨by linarith, hδ⟩
  have hSu (u : ℝ) (hu : u∈S) : |u| *L<1 := by
    have hh : |u|<δ := abs_lt.mpr hu
    exact (mul_le_mul_of_nonneg_right hh.le L.coe_nonneg).trans_lt hsmall
  let A := fun u=>scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2)
  let B := fun u=>scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficientDerivative s β φ u) (k+2)
  obtain ⟨K,H,hbounds⟩ := exists_scalarTransportGaussian_local_bounds s β hβ φ L hφ h0 h1
  let U := S∩{u | ‖A u‖≤K ∧ ‖B u‖≤H}
  have hU : U∈𝓝 (0:ℝ) := inter_mem hS hbounds
  let F := scalarTransportGradientSquare s β φ p
  let c := FRSB.Gamma β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p)
  let C : ℝ≥0 := ⟨max 4 (P+Q),le_max_of_le_left (by norm_num)⟩
  have hC4 : 4≤(C:ℝ) := le_max_left _ _
  have hCPQ : P+Q≤(C:ℝ) := le_max_right _ _
  have hFjoint (u) (hu : u∈S) (x) : DifferentiableAt ℝ (Function.uncurry F) (u,x) := by
    exact (hasFDerivAt_joint_of_parameter_spatial_partials F DF
      (fun v y=>fderiv ℝ (F v) y) S isOpen_Ioo u x hu hDF
      (fun v _ y=>(boundedJets_scalarTransportGradientSquare s β φ p v).1.differentiable (by simp) y |>.hasFDerivAt)
      hcDF (continuous_scalarTransportGradientSquare_fderiv s β hβ φ p).continuousOn).differentiableAt
  have hFpartial (u) (hu : u∈S) (x) : gaussianParameterDerivative F u x=DF u x :=
    gaussianParameterDerivative_eq_actual_partial F DF (fun v y=>fderiv ℝ (F v) y) S isOpen_Ioo u x hu
      hDF (fun v _ y=>(boundedJets_scalarTransportGradientSquare s β φ p v).1.differentiable (by simp) y |>.hasFDerivAt)
      hcDF (continuous_scalarTransportGradientSquare_fderiv s β hβ φ p).continuousOn
  have hmF : Measurable (gaussianParameterDerivative F 0) := by
    have hc : Continuous (fun x : QuantitativePaper.Field (k+3)=>DF 0 x) :=
      hcDF.comp_continuous (continuous_const.prodMk continuous_id) (fun x=>⟨mem_of_mem_nhds hS,mem_univ x⟩)
    have he : gaussianParameterDerivative F 0=DF 0 := funext fun x=>hFpartial 0 (mem_of_mem_nhds hS) x
    rw [he]
    exact hc.measurable
  let N := fun e u=>gaussianLinearMean (fun y=>Real.exp (scalarTransportEuclideanExponent s β φ e u y)*F u y) (A u) 0
  let Z := fun e u=>gaussianLinearMean (fun y=>Real.exp (scalarTransportEuclideanExponent s β φ e u y)) (A u) 0
  let R := fun e=>∫z,Real.exp (scalarTransportEuclideanExponent s β φ e 0 (A 0 z))*(
    DF 0 (A 0 z)+(F 0 (A 0 z)-c)*DV e 0 (A 0 z)+
      ∑i : Fin (k+2),gaussianScoreBilinear (scalarTransportEuclideanExponent s β φ e 0) (F 0)
        (A 0 z) (A 0 (EuclideanSpace.single i 1)) (B 0 (EuclideanSpace.single i 1)) c) ∂fieldGaussian (k+2)
  have hd (e : Bool) : HasDerivAt (fun u=>N e u-c*Z e u) (R e) 0 := by
    let V := scalarTransportEuclideanExponent s β φ e
    have hVjoint (u) (hu : u∈S) (x) : DifferentiableAt ℝ (Function.uncurry V) (u,x) :=
      (hasFDerivAt_joint_of_parameter_spatial_partials V (DV e)
        (fun v y=>fderiv ℝ (V v) y) S isOpen_Ioo u x hu (hDV e)
        (fun v _ y=>(boundedPositiveJets_scalarTransportEuclideanExponent s β φ e v).1.differentiable (by simp) y |>.hasFDerivAt)
        (hcDV e) (continuous_scalarTransportEuclideanExponent_fderiv s β φ e).continuousOn).differentiableAt
    have hVpartial (u) (hu : u∈S) (x) : gaussianParameterDerivative V u x=DV e u x :=
      gaussianParameterDerivative_eq_actual_partial V (DV e) (fun v y=>fderiv ℝ (V v) y) S isOpen_Ioo u x hu
        (hDV e) (fun v _ y=>(boundedPositiveJets_scalarTransportEuclideanExponent s β φ e v).1.differentiable (by simp) y |>.hasFDerivAt)
        (hcDV e) (continuous_scalarTransportEuclideanExponent_fderiv s β φ e).continuousOn
    have hmV : Measurable (gaussianParameterDerivative V 0) := by
      have hc : Continuous (fun x : QuantitativePaper.Field (k+3)=>DV e 0 x) :=
        (hcDV e).comp_continuous (continuous_const.prodMk continuous_id) (fun x=>⟨mem_of_mem_nhds hS,mem_univ x⟩)
      rw [show gaussianParameterDerivative V 0=DV e 0 from funext fun x=>hVpartial 0 (mem_of_mem_nhds hS) x]
      exact hc.measurable
    let dF : ∀u,VectorHeatDatum (fun y=>Real.exp (V u y)*F u y) := fun u=>
      Classical.choice (scalarTransportGaussianSquare_heatData s β φ e p u)
    let dH : ∀u,VectorHeatDatum (fun y=>Real.exp (V u y)) := fun u=>
      Classical.choice (scalarTransportGaussianWeight_heatData s β φ e u)
    have hpF (u) (hu : u∈U) (y) :
        ‖gaussianParameterDerivative (fun v z=>Real.exp (V v z)*F v z) u y‖≤C*Real.exp ((1:ℝ≥0)*‖y‖) := by
      rw [gaussianParameterDerivative_exp_mul V F (hVjoint u hu.1 y) (hFjoint u hu.1 y),
        hFpartial u hu.1 y,hVpartial u hu.1 y,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
      have he : Real.exp (V u y)≤Real.exp ‖y‖ := Real.exp_le_exp.mpr (by
        dsimp only [V]
        rw [scalarTransportEuclideanExponent_eq_actual s β φ L hφ h0 h1 u (hSu u hu.1)]
        exact scalarFiniteEuclideanExponent_le_norm _ _ _ _)
      have hf : ‖F u y‖≤1 := by
        dsimp only [F]
        rw [scalarTransportGradientSquare_eq_actual s β φ L hφ h0 h1 u (hSu u hu.1)]
        exact norm_scalarFiniteGradientSquare_le_one _ _ _ _
      have hfD : ‖F u y*DV e u y‖≤P := by
        rw [norm_mul]
        simpa only [one_mul] using mul_le_mul hf (hbDV e u hu.1 y) (norm_nonneg _) zero_le_one
      have hn := (norm_add_le _ _).trans (add_le_add (hbDF u hu.1 y) hfD)
      simpa only [NNReal.coe_one,one_mul,mul_comm] using mul_le_mul he (hn.trans (by linarith))
        (norm_nonneg _) (Real.exp_pos ‖y‖).le
    have hpH (u) (hu : u∈U) (y) :
        ‖gaussianParameterDerivative (fun v z=>Real.exp (V v z)) u y‖≤C*Real.exp ((1:ℝ≥0)*‖y‖) := by
      rw [gaussianParameterDerivative_exp V (hVjoint u hu.1 y),hVpartial u hu.1 y,
        norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
      have he : Real.exp (V u y)≤Real.exp ‖y‖ := Real.exp_le_exp.mpr (by
        dsimp only [V]
        rw [scalarTransportEuclideanExponent_eq_actual s β φ L hφ h0 h1 u (hSu u hu.1)]
        exact scalarFiniteEuclideanExponent_le_norm _ _ _ _)
      simpa only [NNReal.coe_one,one_mul,mul_comm] using mul_le_mul he
        ((hbDV e u hu.1 y).trans (by linarith)) (norm_nonneg _) (Real.exp_pos ‖y‖).le
    have hh := hasDerivAt_gaussian_centered_parameter_mean V F A B 0 U hU
      (fun u hu=>hVjoint u hu.1) (fun u hu=>hFjoint u hu.1)
      ((boundedPositiveJets_scalarTransportEuclideanExponent s β φ e 0).1.of_le (by simp))
      ((boundedJets_scalarTransportGradientSquare s β φ p 0).1.of_le (by simp))
      hmV hmF dF dH (fun u hu=>hasDerivAt_scalarTransportGaussianHistory s β hβ φ L hφ h0 h1 u (hSu u hu.1))
      C 1 K H (fun u hu=>hu.2.1) (fun u hu=>hu.2.2)
      (fun u hu y=>(norm_scalarTransportGaussianSquare_first_le s β φ L hφ h0 h1 u (hSu u hu.1) e p y).trans (by
        simpa only [NNReal.coe_one,one_mul] using mul_le_mul_of_nonneg_right hC4 (Real.exp_pos ‖y‖).le))
      (fun u hu y=>(norm_scalarTransportGaussianWeight_first_le s β φ L hφ h0 h1 u (hSu u hu.1) e y).trans (by
        simpa only [NNReal.coe_one,one_mul] using mul_le_mul_of_nonneg_right (by linarith : (2:ℝ)≤C) (Real.exp_pos ‖y‖).le))
      hpF hpH 0 c
    apply hh.congr_deriv
    unfold R gaussianExplicitCenteredScore
    simp only [zero_add,hFpartial 0 (mem_of_mem_nhds hS),hVpartial 0 (mem_of_mem_nhds hS)]
    rfl
  have hnorm : ∀ᶠu in 𝓝 (0:ℝ),(∑e : Bool,Z e u)=2 := by
    filter_upwards [hS] with u hu
    simpa only [Z,gaussianLinearMean,A,zero_add] using
      scalarTransportGaussian_normalization s β hβ φ L hφ h0 h1 u (hSu u hu)
  have hh := hasDerivAt_finiteMarkedMean_of_centered N Z R 0 c 2 (by norm_num) hd hnorm
  have hg : (fun u=>FRSB.Gamma β (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
      (scalarLevelTransport φ u (scalarSchemeTransportNode s p)))=ᶠ[𝓝 (0:ℝ)]
      (fun u=>(∑e : Bool,N e u)/(∑e : Bool,Z e u)) := by
    filter_upwards [hS,hnorm] with u hu hn
    rw [hn,scalarTransportGaussian_Gamma s β hβ φ L hφ h0 h1 u (hSu u hu) p]
    dsimp only [N,gaussianLinearMean,A]
    simp only [zero_add]
    ring
  convert! hh.congr_of_eventuallyEq hg using 1
  dsimp only [R,A,B,F,c]
  ring

end QuantitativeFollowup
