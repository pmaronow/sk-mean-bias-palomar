module
public import HexagonPaper.PathHeatSignedSourceFiniteRaw

@[expose] public section

/-! Source-faithful finite clock response. Spatial data, all Gaussian
growth bounds, measurable parameter derivatives and local factor bounds
are proved internally from the source signed jets and genuine clock curve.
Both raw derivatives are retained for later auxiliary integration. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ContDiff BigOperators
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup FourPapersCommon
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]
variable {n m : ℕ}

def pathHeatSourceFiniteNormalizer (A : Field m→L[ℝ]C(X,ℝ))
    (ell : ℝ→C(X,ℝ)→ℝ) (v : ℝ→Fin n→ℝ) (mask : Fin n→Field m)
    (x : Field m) (u : ℝ) : ℝ :=
  gaussianLinearMean (fun y=>Real.exp (ell u (A y))) (pathHeatVarianceFactor v mask u) x

def pathHeatSourceFiniteNumerator (A : Field m→L[ℝ]C(X,ℝ))
    (ell Phi : ℝ→C(X,ℝ)→ℝ) (v : ℝ→Fin n→ℝ) (mask : Fin n→Field m)
    (x : Field m) (u : ℝ) : ℝ :=
  gaussianLinearMean (fun y=>Real.exp (ell u (A y))*Phi u (A y)) (pathHeatVarianceFactor v mask u) x

def pathHeatSourceFiniteExpectation (A : Field m→L[ℝ]C(X,ℝ))
    (ell Phi : ℝ→C(X,ℝ)→ℝ) (v : ℝ→Fin n→ℝ) (mask : Fin n→Field m)
    (x : Field m) (u : ℝ) : ℝ :=
  pathHeatSourceFiniteNumerator A ell Phi v mask x u/pathHeatSourceFiniteNormalizer A ell v mask x u

def pathHeatSourceFiniteDensityScore (A : Field m→L[ℝ]C(X,ℝ))
    (ell : ℝ→C(X,ℝ)→ℝ) (dotell : ℝ×C(X,ℝ)→ℝ)
    (dv : ℝ→Fin n→ℝ) (mask : Fin n→Field m) (u : ℝ) (y : Field m) : ℝ :=
  dotell (u,A y)+(1/2:ℝ)*∑j : Fin m,∑k : Fin m,
    pathHeatVarianceCovarianceDerivative dv mask u j k*
      (vectorHessian (fun z=>ell u (A z)) y (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)+
        fderiv ℝ (fun z=>ell u (A z)) y (EuclideanSpace.single j 1)*
          fderiv ℝ (fun z=>ell u (A z)) y (EuclideanSpace.single k 1))

def pathHeatSourceFiniteCenteredScore (A : Field m→L[ℝ]C(X,ℝ))
    (ell Phi : ℝ→C(X,ℝ)→ℝ) (dotell dotPhi : ℝ×C(X,ℝ)→ℝ)
    (dv : ℝ→Fin n→ℝ) (mask : Fin n→Field m) (u : ℝ) (y : Field m) (center : ℝ) : ℝ :=
  dotPhi (u,A y)+(Phi u (A y)-center)*dotell (u,A y)+
    (1/2:ℝ)*∑j : Fin m,∑k : Fin m,pathHeatVarianceCovarianceDerivative dv mask u j k*
      gaussianScoreBilinear (fun z=>ell u (A z)) (fun z=>Phi u (A z)) y
        (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) center

theorem pathHeat_signed_source_finite_response
    (a b : ℝ) (hab : a≤b) (z : ℝ) (hz : z∈Ioo a b)
    (A : Field m→L[ℝ]C(X,ℝ))
    (ell Phi : ℝ→C(X,ℝ)→ℝ) (dotell dotPhi : ℝ×C(X,ℝ)→ℝ)
    (S P : ℝ×C(X,ℝ)→SignedMeasure X) (M Q : ℝ×C(X,ℝ)→SignedMeasure (X×X))
    (B Ls Lm Lp Lq C0 C1 Dt Dphi : ℝ≥0)
    (hs : PathHeatSignedSpatialBounds ell Phi S P M Q (Icc a b) B Ls Lm Lp Lq C0 C1)
    (ht : PathHeatSignedParameterData ell dotell S (Ioo a b))
    (hp : PathHeatSignedParameterData Phi dotPhi P (Ioo a b))
    (hdt : ∀u∈Ioo a b,∀p,|dotell (u,p)|≤Dt)
    (hdphi : ∀u∈Ioo a b,∀p,|dotPhi (u,p)|≤Dphi)
    (v dv : ℝ→Fin n→ℝ) (mask : Fin n→Field m)
    (hv : ∀u∈Ioo a b,∀i,0<v u i)
    (hdv : ∀u∈Ioo a b,∀i,HasDerivAt (fun t=>v t i) (dv u i) u)
    (hdvc : ∀i,ContinuousAt (fun u=>dv u i) z) (x : Field m) :
    0<pathHeatSourceFiniteNormalizer A ell v mask x z ∧
    HasDerivAt (pathHeatSourceFiniteNormalizer A ell v mask x)
      (∫g,Real.exp (ell z (A (x+pathHeatVarianceFactor v mask z g)))*
        pathHeatSourceFiniteDensityScore A ell dotell dv mask z (x+pathHeatVarianceFactor v mask z g)
        ∂fieldGaussian n) z ∧
    HasDerivAt (pathHeatSourceFiniteNumerator A ell Phi v mask x)
      (∫g,Real.exp (ell z (A (x+pathHeatVarianceFactor v mask z g)))*
        pathHeatSourceFiniteCenteredScore A ell Phi dotell dotPhi dv mask z
          (x+pathHeatVarianceFactor v mask z g) 0 ∂fieldGaussian n) z ∧
    HasDerivAt (pathHeatSourceFiniteExpectation A ell Phi v mask x)
      ((∫g,Real.exp (ell z (A (x+pathHeatVarianceFactor v mask z g)))*
        pathHeatSourceFiniteCenteredScore A ell Phi dotell dotPhi dv mask z
          (x+pathHeatVarianceFactor v mask z g)
          (pathHeatSourceFiniteExpectation A ell Phi v mask x z) ∂fieldGaussian n)/
        pathHeatSourceFiniteNormalizer A ell v mask x z) z := by
  let K : ℝ≥0 := ‖A‖₊
  let f := pathHeatClampedFamily a b hab ell
  let g := pathHeatClampedFamily a b hab Phi
  let V := fun u y=>f u (A y)
  let F := fun u y=>g u (A y)
  let C := pathHeatSourceFiniteGrowthBound B Ls Lm Lp Lq C0 K Dt Dphi
  let R := C1*K
  let data := pathHeat_source_finite_analytic_data a b hab A ell Phi dotell dotPhi S P M Q
    B Ls Lm Lp Lq C0 C1 K Dt Dphi hs ht hp (le_refl ‖A‖) hdt hdphi
  obtain ⟨U₀,Kf,Lf,hU₀,hAf,hBf⟩ := pathHeatVarianceFactor_local_bounds v dv mask z
    (hv z hz) (fun i=>(hdv z hz i).continuousAt) hdvc
  let U := Ioo a b∩U₀
  have hU : U∈𝓝 z := inter_mem (isOpen_Ioo.mem_nhds hz) hU₀
  have sub (u : ℝ) (hu : u∈U) : u∈Ioo a b := hu.1
  let dataU : PathHeatFiniteAnalyticData V F U C R := {
    normalizer := data.normalizer
    numerator := data.numerator
    jointV := fun u hu=>data.jointV u (sub u hu)
    jointF := fun u hu=>data.jointF u (sub u hu)
    spatialV := fun u hu=>data.spatialV u (sub u hu)
    spatialF := fun u hu=>data.spatialF u (sub u hu)
    parameterV := fun u hu=>data.parameterV u (sub u hu)
    parameterF := fun u hu=>data.parameterF u (sub u hu)
    firstNormalizer := fun u hu=>data.firstNormalizer u (sub u hu)
    firstNumerator := fun u hu=>data.firstNumerator u (sub u hu)
    partialNormalizer := fun u hu=>data.partialNormalizer u (sub u hu)
    partialNumerator := fun u hu=>data.partialNumerator u (sub u hu)
  }
  have hvU := fun u (hu : u∈U)=>hv u hu.1
  have hdvU := fun u (hu : u∈U)=>hdv u hu.1
  have hAfU := fun u (hu : u∈U)=>hAf u hu.2
  have hBfU := fun u (hu : u∈U)=>hBf u hu.2
  have hzU := mem_of_mem_nhds hU
  have hZ := hasDerivAt_pathHeat_finiteClock_normalizer V v dv mask z U hU hvU hdvU
    dataU.jointV (dataU.spatialV z hzU) (dataU.parameterV z hzU) dataU.normalizer C R Kf Lf
    hAfU hBfU dataU.firstNormalizer dataU.partialNormalizer x
  have hN := hasDerivAt_pathHeat_finiteClock_numerator V F v dv mask z U hU C R Kf Lf dataU
    hvU hdvU hAfU hBfU x
  have hE := hasDerivAt_pathHeat_finiteClock_response V F v dv mask z U hU hvU hdvU
    dataU.jointV dataU.jointF (dataU.spatialV z hzU) (dataU.spatialF z hzU)
    (dataU.parameterV z hzU) (dataU.parameterF z hzU) dataU.numerator dataU.normalizer
    C R Kf Lf hAfU hBfU dataU.firstNumerator dataU.firstNormalizer
    dataU.partialNumerator dataU.partialNormalizer x
  have heV : V z=fun y=>ell z (A y) := by
    funext y
    simp only [V,f,pathHeatClampedFamily,pathHeatParameterClamp_eq a b hab z ⟨hz.1.le,hz.2.le⟩]
  have heF : F z=fun y=>Phi z (A y) := by
    funext y
    simp only [F,g,pathHeatClampedFamily,pathHeatParameterClamp_eq a b hab z ⟨hz.1.le,hz.2.le⟩]
  have hPV (y : Field m) : gaussianParameterDerivative V z y=dotell (z,A y) := by
    have h := (pathHeat_source_finite_parameter_partials A f
      (pathHeatClampedJoint a b hab dotell) (pathHeatClampedJoint a b hab S)
      (Ioo a b) z (isOpen_Ioo.mem_nhds hz) (pathHeat_clamped_parameter_data a b hab ell dotell S ht)).2.1 y
    simpa only [V,pathHeatClampedJoint,pathHeatParameterClamp_eq a b hab z ⟨hz.1.le,hz.2.le⟩] using h
  have hPF (y : Field m) : gaussianParameterDerivative F z y=dotPhi (z,A y) := by
    have h := (pathHeat_source_finite_parameter_partials A g
      (pathHeatClampedJoint a b hab dotPhi) (pathHeatClampedJoint a b hab P)
      (Ioo a b) z (isOpen_Ioo.mem_nhds hz) (pathHeat_clamped_parameter_data a b hab Phi dotPhi P hp)).2.1 y
    simpa only [F,pathHeatClampedJoint,pathHeatParameterClamp_eq a b hab z ⟨hz.1.le,hz.2.le⟩] using h
  have hlocal : ∀ᶠu in 𝓝 z,V u=(fun y=>ell u (A y)) ∧ F u=(fun y=>Phi u (A y)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with u hu
    constructor <;> funext y <;>
      simp only [V,F,f,g,pathHeatClampedFamily,pathHeatParameterClamp_eq a b hab u ⟨hu.1.le,hu.2.le⟩]
  have hEZ : pathHeatSourceFiniteNormalizer A ell v mask x =ᶠ[𝓝 z]
      (fun u=>gaussianLinearMean (fun y=>Real.exp (V u y)) (pathHeatVarianceFactor v mask u) x) :=
    hlocal.mono fun u hu=>by simp only [pathHeatSourceFiniteNormalizer,hu.1]
  have hEN : pathHeatSourceFiniteNumerator A ell Phi v mask x =ᶠ[𝓝 z]
      (fun u=>gaussianLinearMean (fun y=>Real.exp (V u y)*F u y) (pathHeatVarianceFactor v mask u) x) :=
    hlocal.mono fun u hu=>by simp only [pathHeatSourceFiniteNumerator,hu.1,hu.2]
  have hEE : pathHeatSourceFiniteExpectation A ell Phi v mask x =ᶠ[𝓝 z]
      (fun u=>gaussianLinearNormalizedMean (fun y=>Real.exp (V u y)*F u y)
        (fun y=>Real.exp (V u y)) (pathHeatVarianceFactor v mask u) x) :=
    hlocal.mono fun u hu=>by simp only [pathHeatSourceFiniteExpectation,pathHeatSourceFiniteNumerator,
      pathHeatSourceFiniteNormalizer,gaussianLinearNormalizedMean,hu.1,hu.2]
  have heCenter : gaussianLinearNormalizedMean (fun y=>Real.exp (V z y)*F z y)
      (fun y=>Real.exp (V z y)) (pathHeatVarianceFactor v mask z) x=
        pathHeatSourceFiniteExpectation A ell Phi v mask x z := by
    simp only [heV,heF,pathHeatSourceFiniteExpectation,pathHeatSourceFiniteNumerator,
      pathHeatSourceFiniteNormalizer,gaussianLinearNormalizedMean]
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [pathHeatSourceFiniteNormalizer,heV] using
      gaussianLinear_exp_normalizer_pos (V z) (dataU.normalizer z) (pathHeatVarianceFactor v mask z) x
  · apply (hZ.congr_of_eventuallyEq hEZ).congr_deriv
    simp only [pathHeatFiniteNormalizerScore,pathHeatSourceFiniteDensityScore,heV,hPV]
  · apply (hN.congr_of_eventuallyEq hEN).congr_deriv
    simp only [pathHeatSourceFiniteCenteredScore,heV,heF,hPV,hPF,sub_zero]
  · apply (hE.congr_of_eventuallyEq hEE).congr_deriv
    simp_rw [heCenter]
    simp only [pathHeatSourceFiniteCenteredScore,gaussianExplicitCenteredScore,heV,heF,hPV,hPF,
      pathHeatSourceFiniteNormalizer]

end HexagonPaper
