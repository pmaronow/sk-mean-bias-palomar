module
public import HexagonPaper.PathHeatSignedSourceClamp
public import HexagonPaper.PathHeatFiniteNormalizer
public import HexagonPaper.PathHeatSignedFiniteScore

@[expose] public section

/-! All finite analytic differentiation inputs are constructed from the
source's signed jets and compact-interval bounds, after internal clamping.
The data are an output, never a premise of the source response theorem. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ContDiff BigOperators
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup FourPapersCommon
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]
variable {n : ℕ}

def pathHeatSourceFiniteGrowthBound (B Ls Lm Lp Lq C0 K Dt Dphi : ℝ≥0) : ℝ≥0 :=
  pathHeatFiniteGrowthBound 1 (Ls*K) (Lm*K^2) 0 0 C0+
  pathHeatFiniteGrowthBound B (Ls*K) (Lm*K^2) (Lp*K) (Lq*K^2) C0+
  pathHeatFiniteParameterGrowthBound B Dt Dphi C0

structure PathHeatFiniteAnalyticData (V F : ℝ→Field n→ℝ) (U : Set ℝ)
    (C R : ℝ≥0) where
  normalizer : ∀u,VectorHeatDatum (fun y=>Real.exp (V u y))
  numerator : ∀u,VectorHeatDatum (fun y=>Real.exp (V u y)*F u y)
  jointV : ∀u∈U,∀y,DifferentiableAt ℝ (Function.uncurry V) (u,y)
  jointF : ∀u∈U,∀y,DifferentiableAt ℝ (Function.uncurry F) (u,y)
  spatialV : ∀u∈U,ContDiff ℝ 2 (V u)
  spatialF : ∀u∈U,ContDiff ℝ 2 (F u)
  parameterV : ∀u∈U,Measurable (gaussianParameterDerivative V u)
  parameterF : ∀u∈U,Measurable (gaussianParameterDerivative F u)
  firstNormalizer : ∀u∈U,∀y,‖fderiv ℝ (fun x=>Real.exp (V u x)) y‖≤C*Real.exp (R*‖y‖)
  firstNumerator : ∀u∈U,∀y,‖fderiv ℝ (fun x=>Real.exp (V u x)*F u x) y‖≤C*Real.exp (R*‖y‖)
  partialNormalizer : ∀u∈U,∀y,‖gaussianParameterDerivative (fun z x=>Real.exp (V z x)) u y‖≤C*Real.exp (R*‖y‖)
  partialNumerator : ∀u∈U,∀y,‖gaussianParameterDerivative (fun z x=>Real.exp (V z x)*F z x) u y‖≤C*Real.exp (R*‖y‖)

def pathHeat_source_finite_analytic_data
    (a b : ℝ) (hab : a≤b) (A : Field n→L[ℝ]C(X,ℝ))
    (ell Phi : ℝ→C(X,ℝ)→ℝ) (dotell dotPhi : ℝ×C(X,ℝ)→ℝ)
    (S P : ℝ×C(X,ℝ)→SignedMeasure X) (M Q : ℝ×C(X,ℝ)→SignedMeasure (X×X))
    (B Ls Lm Lp Lq C0 C1 K Dt Dphi : ℝ≥0)
    (hs : PathHeatSignedSpatialBounds ell Phi S P M Q (Icc a b) B Ls Lm Lp Lq C0 C1)
    (ht : PathHeatSignedParameterData ell dotell S (Ioo a b))
    (hp : PathHeatSignedParameterData Phi dotPhi P (Ioo a b))
    (hA : ‖A‖≤K) (hdt : ∀u∈Ioo a b,∀p,|dotell (u,p)|≤Dt)
    (hdphi : ∀u∈Ioo a b,∀p,|dotPhi (u,p)|≤Dphi) :
    PathHeatFiniteAnalyticData
      (fun u y=>pathHeatClampedFamily a b hab ell u (A y))
      (fun u y=>pathHeatClampedFamily a b hab Phi u (A y)) (Ioo a b)
      (pathHeatSourceFiniteGrowthBound B Ls Lm Lp Lq C0 K Dt Dphi) (C1*K) := by
  let f := pathHeatClampedFamily a b hab ell
  let g := pathHeatClampedFamily a b hab Phi
  let df := pathHeatClampedJoint a b hab dotell
  let dg := pathHeatClampedJoint a b hab dotPhi
  let s := pathHeatClampedJoint a b hab S
  let p := pathHeatClampedJoint a b hab P
  have htf : PathHeatSignedParameterData f df s (Ioo a b) := pathHeat_clamped_parameter_data a b hab ell dotell S ht
  have htg : PathHeatSignedParameterData g dg p (Ioo a b) := pathHeat_clamped_parameter_data a b hab Phi dotPhi P hp
  let d := pathHeat_signed_source_finite_data a b hab A ell Phi S P M Q B Ls Lm Lp Lq C0 C1 K hs hA
  let C := pathHeatSourceFiniteGrowthBound B Ls Lm Lp Lq C0 K Dt Dphi
  have fields (u : ℝ) := pathHeat_signed_source_finite_data_fields
    a b hab A ell Phi S P M Q B Ls Lm Lp Lq C0 C1 K hs hA u
  have hcH : (pathHeatFiniteGrowthBound 1 (Ls*K) (Lm*K^2) 0 0 C0:ℝ)≤C := by
    dsimp [C,pathHeatSourceFiniteGrowthBound]
    linarith [(pathHeatFiniteGrowthBound B (Ls*K) (Lm*K^2) (Lp*K) (Lq*K^2) C0).coe_nonneg,
      (pathHeatFiniteParameterGrowthBound B Dt Dphi C0).coe_nonneg]
  have hcF : (pathHeatFiniteGrowthBound B (Ls*K) (Lm*K^2) (Lp*K) (Lq*K^2) C0:ℝ)≤C := by
    dsimp [C,pathHeatSourceFiniteGrowthBound]
    linarith [(pathHeatFiniteGrowthBound 1 (Ls*K) (Lm*K^2) 0 0 C0).coe_nonneg,
      (pathHeatFiniteParameterGrowthBound B Dt Dphi C0).coe_nonneg]
  have hcP : (pathHeatFiniteParameterGrowthBound B Dt Dphi C0:ℝ)≤C := by
    dsimp [C,pathHeatSourceFiniteGrowthBound]
    linarith [(pathHeatFiniteGrowthBound 1 (Ls*K) (Lm*K^2) 0 0 C0).coe_nonneg,
      (pathHeatFiniteGrowthBound B (Ls*K) (Lm*K^2) (Lp*K) (Lq*K^2) C0).coe_nonneg]
  have part (u : ℝ) (hu : u∈Ioo a b) :=
    pathHeat_source_finite_parameter_partials A f df s (Ioo a b) u (isOpen_Ioo.mem_nhds hu) htf
  have partg (u : ℝ) (hu : u∈Ioo a b) :=
    pathHeat_source_finite_parameter_partials A g dg p (Ioo a b) u (isOpen_Ioo.mem_nhds hu) htg
  have spatial (u : ℝ) (hu : u∈Ioo a b) : ContDiff ℝ 2 (fun y=>f u (A y)) ∧
      ContDiff ℝ 2 (fun y=>g u (A y)) := by
    have hu' : u∈Icc a b := ⟨hu.1.le,hu.2.le⟩
    constructor
    · simpa only [f,pathHeatClampedFamily,pathHeatParameterClamp_eq a b hab u hu'] using
        contDiff_two_pathHeatPullback A (ell u) (fun q=>S (u,q)) (fun q=>M (u,q))
          (hs.ell_derivative u hu') (hs.score_derivative u hu') (hs.hessian_continuous u hu')
    · simpa only [g,pathHeatClampedFamily,pathHeatParameterClamp_eq a b hab u hu'] using
        contDiff_two_pathHeatPullback A (Phi u) (fun q=>P (u,q)) (fun q=>Q (u,q))
          (hs.phi_derivative u hu') (hs.phi_score_derivative u hu') (hs.phi_hessian_continuous u hu')
  have hpartialAll (u : ℝ) (hu : u∈Ioo a b) (y : Field n) :=
    pathHeat_source_finite_parameter_bounds A f g df dg s p (Ioo a b) u
      (isOpen_Ioo.mem_nhds hu) htf htg B Dt Dphi C0 C1 K hA
      (by simpa only [f,pathHeatClampedFamily,pathHeatParameterClamp_eq a b hab u ⟨hu.1.le,hu.2.le⟩]
        using hs.ell_bound u ⟨hu.1.le,hu.2.le⟩)
      (by simpa only [g,pathHeatClampedFamily,pathHeatParameterClamp_eq a b hab u ⟨hu.1.le,hu.2.le⟩]
        using hs.phi_bound u ⟨hu.1.le,hu.2.le⟩)
      (by simpa only [df,pathHeatClampedJoint,pathHeatParameterClamp_eq a b hab u ⟨hu.1.le,hu.2.le⟩]
        using hdt u hu)
      (by simpa only [dg,pathHeatClampedJoint,pathHeatParameterClamp_eq a b hab u ⟨hu.1.le,hu.2.le⟩]
        using hdphi u hu) y
  refine {
    normalizer := fun u=>(d u).1
    numerator := fun u=>(d u).2
    jointV := fun u hu=>(part u hu).1
    jointF := fun u hu=>(partg u hu).1
    spatialV := fun u hu=>(spatial u hu).1
    spatialF := fun u hu=>(spatial u hu).2
    parameterV := fun u hu=>(part u hu).2.2
    parameterF := fun u hu=>(partg u hu).2.2
    firstNormalizer := ?_
    firstNumerator := ?_
    partialNormalizer := ?_
    partialNumerator := ?_
  }
  · intro u hu y
    have h := (d u).1.first_bound y
    rw [(fields u).1,(fields u).2.1] at h
    exact h.trans (mul_le_mul_of_nonneg_right hcH (Real.exp_pos _).le)
  · intro u hu y
    have h := (d u).2.first_bound y
    rw [(fields u).2.2.1,(fields u).2.2.2] at h
    exact h.trans (mul_le_mul_of_nonneg_right hcF (Real.exp_pos _).le)
  · intro u hu y
    exact (hpartialAll u hu y).1.trans (mul_le_mul_of_nonneg_right hcP (Real.exp_pos _).le)
  · intro u hu y
    exact (hpartialAll u hu y).2.trans (mul_le_mul_of_nonneg_right hcP (Real.exp_pos _).le)

end HexagonPaper
