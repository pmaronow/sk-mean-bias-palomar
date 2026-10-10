module
public import HexagonPaper.PathHeatContinuousSignedSource
public import HexagonPaper.PathHeatSignedSourceClamp

@[expose] public section

/-! The actual source jets on the compact parameter interval, with
untouched auxiliary Gaussian and counting coordinates. Projection extends
only the parameter; all finite analytic data are derived from these jets. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval NNReal
namespace HexagonPaper
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L : ℕ} {a b : ℝ}

def pathHeatWienerRealFamily (a b : ℝ) (hab : a≤b)
    (f : Icc a b×((E×K)×C(Fin L×I,ℝ))→ℝ) (ω : E×K)
    (z : ℝ) (p : C(Fin L×I,ℝ)) : ℝ := f (projIcc a b hab z,(ω,p))

def pathHeatWienerRealJoint {Y : Type*} (a b : ℝ) (hab : a≤b)
    (f : Icc a b×((E×K)×C(Fin L×I,ℝ))→Y) (ω : E×K)
    (v : ℝ×C(Fin L×I,ℝ)) : Y := f (projIcc a b hab v.1,(ω,v.2))

def pathHeatWienerAuxGrowthConstant (C : ℝ≥0) (ω : E×K) : ℝ≥0 := C*(1+‖ω.1‖₊)

structure PathHeatWienerAnalyticSource
    (a b : ℝ) (hab : a≤b)
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin L×I,ℝ))) (Fin L×I))
    (C : ℝ≥0) : Prop where
  ell_derivative : ∀z ω p,HasFDerivAt (fun q=>d.ell (z,(ω,q)))
    (pathHeatSignedScore (d.S (z,(ω,p)))) p
  phi_derivative : ∀z ω p,HasFDerivAt (fun q=>d.phi (z,(ω,q)))
    (pathHeatSignedScore (d.P (z,(ω,p)))) p
  score_derivative : ∀z ω p,HasFDerivAt (fun q=>pathHeatSignedScore (d.S (z,(ω,q))))
    (pathHeatSignedHessian (d.M (z,(ω,p)))) p
  phi_score_derivative : ∀z ω p,HasFDerivAt (fun q=>pathHeatSignedScore (d.P (z,(ω,q))))
    (pathHeatSignedHessian (d.Q (z,(ω,p)))) p
  ell_parameter : ∀ω z,z∈Ioo a b→∀p,
    HasDerivAt (fun u=>pathHeatWienerRealFamily a b hab d.ell ω u p)
      (pathHeatWienerRealJoint a b hab d.dotell ω (z,p)) z
  phi_parameter : ∀ω z,z∈Ioo a b→∀p,
    HasDerivAt (fun u=>pathHeatWienerRealFamily a b hab d.phi ω u p)
      (pathHeatWienerRealJoint a b hab d.dotphi ω (z,p)) z
  ell_growth : ∀z ω p,|d.ell (z,(ω,p))|≤C*(1+‖ω.1‖+‖p‖)

theorem continuous_pathHeatWienerRealJointMap (a b : ℝ) (hab : a≤b) (ω : E×K) :
    Continuous (fun v : ℝ×C(Fin L×I,ℝ)=>(projIcc a b hab v.1,(ω,v.2))) :=
  (continuous_projIcc.comp continuous_fst).prodMk (continuous_const.prodMk continuous_snd)

theorem pathHeatWiener_source_spatial_bounds (hab : a≤b)
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin L×I,ℝ))) (Fin L×I))
    (C : ℝ≥0) (h : PathHeatWienerAnalyticSource a b hab d C) (ω : E×K) :
    PathHeatSignedSpatialBounds (pathHeatWienerRealFamily a b hab d.ell ω)
      (pathHeatWienerRealFamily a b hab d.phi ω)
      (pathHeatWienerRealJoint a b hab d.S ω) (pathHeatWienerRealJoint a b hab d.P ω)
      (pathHeatWienerRealJoint a b hab d.M ω) (pathHeatWienerRealJoint a b hab d.Q ω)
      (Icc a b) d.B d.Ds d.Dm d.Dp d.Dq (pathHeatWienerAuxGrowthConstant C ω) C := by
  have hc (z : ℝ) : Continuous (fun p : C(Fin L×I,ℝ)=>(projIcc a b hab z,(ω,p))) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  constructor
  · intro z hz p
    change HasFDerivAt (fun q=>d.ell (projIcc a b hab z,(ω,q)))
      (pathHeatSignedScore (d.S (projIcc a b hab z,(ω,p)))) p
    exact h.ell_derivative (projIcc a b hab z) ω p
  · intro z hz p
    change HasFDerivAt (fun q=>d.phi (projIcc a b hab z,(ω,q)))
      (pathHeatSignedScore (d.P (projIcc a b hab z,(ω,p)))) p
    exact h.phi_derivative (projIcc a b hab z) ω p
  · intro z hz p
    change HasFDerivAt (fun q=>pathHeatSignedScore (d.S (projIcc a b hab z,(ω,q))))
      (pathHeatSignedHessian (d.M (projIcc a b hab z,(ω,p)))) p
    exact h.score_derivative (projIcc a b hab z) ω p
  · intro z hz p
    change HasFDerivAt (fun q=>pathHeatSignedScore (d.P (projIcc a b hab z,(ω,q))))
      (pathHeatSignedHessian (d.Q (projIcc a b hab z,(ω,p)))) p
    exact h.phi_score_derivative (projIcc a b hab z) ω p
  · intro z hz p
    exact (d.continuous_M (projIcc a b hab z,(ω,p))).comp ((hc z).tendsto p)
  · intro z hz p
    exact (d.continuous_Q (projIcc a b hab z,(ω,p))).comp ((hc z).tendsto p)
  · intro z hz p;exact d.bound_S (projIcc a b hab z,(ω,p))
  · intro z hz p;exact d.bound_M (projIcc a b hab z,(ω,p))
  · intro z hz p;exact d.bound_P (projIcc a b hab z,(ω,p))
  · intro z hz p;exact d.bound_Q (projIcc a b hab z,(ω,p))
  · intro z hz p;exact d.bound_phi (projIcc a b hab z,(ω,p))
  · intro z hz p
    change |d.ell (projIcc a b hab z,(ω,p))|≤(pathHeatWienerAuxGrowthConstant C ω:ℝ)+C*‖p‖
    calc
      _ ≤ C*(1+‖ω.1‖+‖p‖) := h.ell_growth (projIcc a b hab z) ω p
      _ = _ := by
        simp only [pathHeatWienerAuxGrowthConstant,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_one,coe_nnnorm]
        ring

theorem pathHeatWiener_source_parameter_data (hab : a≤b)
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin L×I,ℝ))) (Fin L×I))
    (C : ℝ≥0) (h : PathHeatWienerAnalyticSource a b hab d C) (ω : E×K) :
    PathHeatSignedParameterData (pathHeatWienerRealFamily a b hab d.ell ω)
      (pathHeatWienerRealJoint a b hab d.dotell ω) (pathHeatWienerRealJoint a b hab d.S ω) (Ioo a b) ∧
    PathHeatSignedParameterData (pathHeatWienerRealFamily a b hab d.phi ω)
      (pathHeatWienerRealJoint a b hab d.dotphi ω) (pathHeatWienerRealJoint a b hab d.P ω) (Ioo a b) := by
  have hc := continuous_pathHeatWienerRealJointMap (L:=L) a b hab ω
  constructor
  · exact ⟨h.ell_parameter ω,fun z _ p=>h.ell_derivative _ ω p,
      fun z _ p=>(d.continuous_dotell.comp hc).continuousAt,
      fun z _ p=>(d.continuous_S _).comp hc.continuousAt.tendsto⟩
  · exact ⟨h.phi_parameter ω,fun z _ p=>h.phi_derivative _ ω p,
      fun z _ p=>(d.continuous_dotphi.comp hc).continuousAt,
      fun z _ p=>(d.continuous_P _).comp hc.continuousAt.tendsto⟩

end HexagonPaper
