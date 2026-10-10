module
public import HexagonPaper.PathHeatFiniteParameterBounds
public import HexagonPaper.PathHeatSignedFiniteUniform
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-! Extension of source families by parameter projection. All global
spatial heat data are derived from source bounds on the closed interval.
On its interior the extended family has the actual source derivative. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace HexagonPaper
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]
variable {n : ℕ}

def pathHeatParameterClamp (a b : ℝ) (hab : a≤b) (z : ℝ) : ℝ :=
  projIcc a b hab z

@[simp] theorem pathHeatParameterClamp_eq (a b : ℝ) (hab : a≤b) (z : ℝ)
    (hz : z∈Icc a b) : pathHeatParameterClamp a b hab z=z := by
  simp only [pathHeatParameterClamp,projIcc_of_mem hab hz]

theorem continuous_pathHeatParameterClamp (a b : ℝ) (hab : a≤b) :
    Continuous (pathHeatParameterClamp a b hab) :=
  continuous_subtype_val.comp continuous_projIcc

theorem hasDerivAt_pathHeatParameterClamp (a b : ℝ) (hab : a≤b) (z : ℝ)
    (hz : z∈Ioo a b) : HasDerivAt (pathHeatParameterClamp a b hab) 1 z := by
  apply (hasDerivAt_id z).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hz] with u hu
  exact pathHeatParameterClamp_eq a b hab u ⟨hu.1.le,hu.2.le⟩

def pathHeatClampedFamily {Y : Type*} (a b : ℝ) (hab : a≤b)
    (f : ℝ→Y→ℝ) : ℝ→Y→ℝ := fun z p=>f (pathHeatParameterClamp a b hab z) p

def pathHeatClampedJoint {Y Z : Type*} (a b : ℝ) (hab : a≤b)
    (f : ℝ×Y→Z) : ℝ×Y→Z := fun v=>f (pathHeatParameterClamp a b hab v.1,v.2)

theorem pathHeat_clamped_parameter_data
    (a b : ℝ) (hab : a≤b)
    (f : ℝ→C(X,ℝ)→ℝ) (dot : ℝ×C(X,ℝ)→ℝ)
    (S : ℝ×C(X,ℝ)→SignedMeasure X)
    (h : PathHeatSignedParameterData f dot S (Ioo a b)) :
    PathHeatSignedParameterData (pathHeatClampedFamily a b hab f)
      (pathHeatClampedJoint a b hab dot) (pathHeatClampedJoint a b hab S) (Ioo a b) := by
  have hc := continuous_pathHeatParameterClamp a b hab
  have hp : Continuous (fun v : ℝ×C(X,ℝ)=>
      (pathHeatParameterClamp a b hab v.1,v.2)) := (hc.comp continuous_fst).prodMk continuous_snd
  constructor
  · intro z hz p
    change HasDerivAt (fun u=>f (pathHeatParameterClamp a b hab u) p)
      (dot (pathHeatParameterClamp a b hab z,p)) z
    rw [pathHeatParameterClamp_eq a b hab z ⟨hz.1.le,hz.2.le⟩]
    apply (h.parameter z hz p).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hz] with u hu
    rw [pathHeatParameterClamp_eq a b hab u ⟨hu.1.le,hu.2.le⟩]
  · intro z hz p
    change HasFDerivAt (f (pathHeatParameterClamp a b hab z))
      (pathHeatSignedScore (S (pathHeatParameterClamp a b hab z,p))) p
    rw [pathHeatParameterClamp_eq a b hab z ⟨hz.1.le,hz.2.le⟩]
    exact h.spatial z hz p
  · intro z hz p
    have hpz : Tendsto (fun v : ℝ×C(X,ℝ)=>
        (pathHeatParameterClamp a b hab v.1,v.2)) (𝓝 (z,p)) (𝓝 (z,p)) := by
      simpa only [pathHeatParameterClamp_eq a b hab z ⟨hz.1.le,hz.2.le⟩]
        using hp.continuousAt.tendsto (x:=(z,p))
    change Tendsto (fun v=>dot (pathHeatParameterClamp a b hab v.1,v.2))
      (𝓝 (z,p)) (𝓝 (dot (pathHeatParameterClamp a b hab z,p)))
    rw [pathHeatParameterClamp_eq a b hab z ⟨hz.1.le,hz.2.le⟩]
    exact (h.dot_continuous z hz p).tendsto.comp hpz
  · intro z hz p
    have hpz : Tendsto (fun v : ℝ×C(X,ℝ)=>
        (pathHeatParameterClamp a b hab v.1,v.2)) (𝓝 (z,p)) (𝓝 (z,p)) := by
      simpa only [pathHeatParameterClamp_eq a b hab z ⟨hz.1.le,hz.2.le⟩]
        using hp.continuousAt.tendsto (x:=(z,p))
    have hd := (h.score_continuous z hz p).comp hpz
    simpa only [Function.comp_def,pathHeatClampedJoint,
      pathHeatParameterClamp_eq a b hab z ⟨hz.1.le,hz.2.le⟩] using hd

structure PathHeatSignedSpatialBounds
    (ell Phi : ℝ→C(X,ℝ)→ℝ) (S P : ℝ×C(X,ℝ)→SignedMeasure X)
    (M Q : ℝ×C(X,ℝ)→SignedMeasure (X×X)) (I : Set ℝ)
    (B Ls Lm Lp Lq C0 C1 : ℝ≥0) : Prop where
  ell_derivative : ∀z∈I,∀p,HasFDerivAt (ell z) (pathHeatSignedScore (S (z,p))) p
  phi_derivative : ∀z∈I,∀p,HasFDerivAt (Phi z) (pathHeatSignedScore (P (z,p))) p
  score_derivative : ∀z∈I,∀p,HasFDerivAt (fun q=>pathHeatSignedScore (S (z,q)))
    (pathHeatSignedHessian (M (z,p))) p
  phi_score_derivative : ∀z∈I,∀p,HasFDerivAt (fun q=>pathHeatSignedScore (P (z,q)))
    (pathHeatSignedHessian (Q (z,p))) p
  hessian_continuous : ∀z∈I,∀p,Tendsto (fun q=>signedTV (M (z,q)-M (z,p))) (𝓝 p) (𝓝 0)
  phi_hessian_continuous : ∀z∈I,∀p,Tendsto (fun q=>signedTV (Q (z,q)-Q (z,p))) (𝓝 p) (𝓝 0)
  score_bound : ∀z∈I,∀p,signedTV (S (z,p))≤Ls
  hessian_bound : ∀z∈I,∀p,signedTV (M (z,p))≤Lm
  phi_score_bound : ∀z∈I,∀p,signedTV (P (z,p))≤Lp
  phi_hessian_bound : ∀z∈I,∀p,signedTV (Q (z,p))≤Lq
  phi_bound : ∀z∈I,∀p,|Phi z p|≤B
  ell_bound : ∀z∈I,∀p,|ell z p|≤C0+C1*‖p‖

def pathHeat_signed_source_finite_data
    (a b : ℝ) (hab : a≤b) (A : Field n→L[ℝ]C(X,ℝ))
    (ell Phi : ℝ→C(X,ℝ)→ℝ) (S P : ℝ×C(X,ℝ)→SignedMeasure X)
    (M Q : ℝ×C(X,ℝ)→SignedMeasure (X×X))
    (B Ls Lm Lp Lq C0 C1 K : ℝ≥0)
    (h : PathHeatSignedSpatialBounds ell Phi S P M Q (Icc a b) B Ls Lm Lp Lq C0 C1)
    (hA : ‖A‖≤K) (z : ℝ) :
    VectorHeatDatum (fun x=>Real.exp (pathHeatClampedFamily a b hab ell z (A x))) ×
    VectorHeatDatum (fun x=>Real.exp (pathHeatClampedFamily a b hab ell z (A x))*
      pathHeatClampedFamily a b hab Phi z (A x)) :=
  let t := pathHeatParameterClamp a b hab z
  let ht : t∈Icc a b := (projIcc a b hab z).property
  pathHeat_finiteData_from_signedJets A (ell t) (Phi t)
    (fun p=>S (t,p)) (fun p=>P (t,p)) (fun p=>M (t,p)) (fun p=>Q (t,p))
    (h.ell_derivative t ht) (h.phi_derivative t ht)
    (h.score_derivative t ht) (h.phi_score_derivative t ht)
    (h.hessian_continuous t ht) (h.phi_hessian_continuous t ht)
    B Ls Lm Lp Lq C0 C1 K
    (h.score_bound t ht) (h.hessian_bound t ht)
    (h.phi_score_bound t ht) (h.phi_hessian_bound t ht)
    (h.phi_bound t ht) (h.ell_bound t ht) hA

theorem pathHeat_signed_source_finite_data_fields
    (a b : ℝ) (hab : a≤b) (A : Field n→L[ℝ]C(X,ℝ))
    (ell Phi : ℝ→C(X,ℝ)→ℝ) (S P : ℝ×C(X,ℝ)→SignedMeasure X)
    (M Q : ℝ×C(X,ℝ)→SignedMeasure (X×X))
    (B Ls Lm Lp Lq C0 C1 K : ℝ≥0)
    (h : PathHeatSignedSpatialBounds ell Phi S P M Q (Icc a b) B Ls Lm Lp Lq C0 C1)
    (hA : ‖A‖≤K) (z : ℝ) :
    let d := pathHeat_signed_source_finite_data a b hab A ell Phi S P M Q
      B Ls Lm Lp Lq C0 C1 K h hA z
    d.1.growthBound=pathHeatFiniteGrowthBound 1 (Ls*K) (Lm*K^2) 0 0 C0 ∧
    d.1.rate=C1*K ∧
    d.2.growthBound=pathHeatFiniteGrowthBound B (Ls*K) (Lm*K^2) (Lp*K) (Lq*K^2) C0 ∧
    d.2.rate=C1*K := by
  dsimp only
  simp [pathHeat_signed_source_finite_data,pathHeat_finiteData_from_signedJets,
    pathHeat_heatDatum_of_bounded_finite_jets,pathHeatFiniteGrowthBound]

end HexagonPaper
