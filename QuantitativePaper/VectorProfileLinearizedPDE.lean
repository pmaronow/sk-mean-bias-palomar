module
public import QuantitativePaper.VectorProfileTimePullbacks
public import QuantitativePaper.VectorProfileRawTraceCalculus
public import FourPapersCommon.PartialGradientCommutation
public import FourPapersCommon.RealParameterCommutation

@[expose] public section

/-! The literal first profile variation satisfies the linearized finite-cell
Parisi PDE. Mixed time/profile/spatial derivatives commute by the proved
actual joint Gaussian smoothness; no evolution equation is supplied. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem hasDerivAt_vectorLaplacian_parameter (U : ℝ×Field n→ℝ)
    (a : ℝ) (x : Field n) (hU : ContDiffAt ℝ ∞ U (a,x)) :
    HasDerivAt (fun θ=>vectorLaplacian (fun y=>U (θ,y)) x)
      (vectorLaplacian (fun y=>deriv (fun θ=>U (θ,y)) a) x) a := by
  have hd:=hasDerivAt_euclideanOperatorTrace (hasDerivAt_partial_hessian U a x hU)
  simpa only [euclideanOperatorTrace_hessian_eq_laplacian] using hd

theorem vectorProfileCellPotentialFirstVariation_time_PDE (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    (a : VectorProfileCellParameter n) (hq : a.1<s₀.q (i+1))
    (hθ : a.2.1∈Ioo (0:ℝ) 1) (x : Field n) :
    deriv (fun q=>vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,a.2) x) a.1=
      -((1-t)*β^2)/2*(
        vectorLaplacian (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x+
        2*vectorProfileMass s₀ s₁ a.2.1 i*
          inner ℝ (gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x)
            (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x)+
        (s₁.m i-s₀.m i)*‖gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x‖^2) := by
  let U : ℝ×Field n→ℝ:=fun z=>
    vectorProfileCellJointPotential s₀ s₁ β t i ((a.1,z.1,a.2.2),z.2)
  have hU : ContDiffAt ℝ ∞ U (a.2.1,x):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((a.1,z.1,a.2.2),z.2))
    (g := vectorProfileCellJointPotential s₀ s₁ β t i) (a.2.1,x)
    (contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi (a,x) hq hθ)
    (by fun_prop)
  have hLap:=hasDerivAt_vectorLaplacian_parameter U a.2.1 x hU
  have hG:=hasDerivAt_partial_gradient U a.2.1 x hU
  have hSq : HasDerivAt (fun θ=>‖gradient (fun y=>U (θ,y)) x‖^2)
      (2*inner ℝ (gradient (fun y=>U (a.2.1,y)) x)
        (gradient (fun y=>deriv (fun θ=>U (θ,y)) a.2.1) x)) a.2.1 := by
    convert hG.inner ℝ hG using 1
    · simp only [real_inner_self_eq_norm_sq]
    · rw [real_inner_comm]
      ring
  have hMass : HasDerivAt (fun θ=>vectorProfileMass s₀ s₁ θ i) (s₁.m i-s₀.m i) a.2.1 := by
    unfold vectorProfileMass
    convert ((hasDerivAt_const a.2.1 1).sub (hasDerivAt_id a.2.1)).mul_const (s₀.m i) |>.add
      ((hasDerivAt_id a.2.1).mul_const (s₁.m i)) using 1
    · ext θ
      simp only [Pi.add_apply,Pi.sub_apply,id_eq]
    · ring
  have hR:=(hLap.add (hMass.mul hSq)).const_mul (-((1-t)*β^2)/2)
  simp only [Pi.add_apply,Pi.mul_apply] at hR
  let V : ℝ×ℝ→ℝ:=fun z=>vectorProfileCellJointPotential s₀ s₁ β t i ((z.1,z.2,a.2.2),x)
  have hV : ContDiffAt ℝ ∞ V (a.1,a.2.1):=ContDiffAt.comp
    (f := fun z : ℝ×ℝ=>((z.1,z.2,a.2.2),x))
    (g := vectorProfileCellJointPotential s₀ s₁ β t i) (a.1,a.2.1)
    (contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi (a,x) hq hθ)
    (by fun_prop)
  have hEq : (fun θ=>deriv (fun q=>V (q,θ)) a.1)=ᶠ[𝓝 a.2.1]
      (fun θ=>-((1-t)*β^2)/2*(vectorLaplacian (fun y=>U (θ,y)) x+
        vectorProfileMass s₀ s₁ θ i*‖gradient (fun y=>U (θ,y)) x‖^2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ hθ'
    exact (hasDerivAt_vectorProfilePhysicalCell_PDE s₀ s₁ β t hβ ht i a.1 θ
      ⟨hθ'.1.le,hθ'.2.le⟩ hq a.2.2 x).deriv
  have hComm:=deriv_real_parameters_commute V a.1 a.2.1 hV
  rw [hEq.deriv_eq,hR.deriv] at hComm
  change deriv (fun q=>vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,a.2) x) a.1=_ at hComm
  have hP : (fun y=>deriv (fun θ=>U (θ,y)) a.2.1)=
      vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a := rfl
  have hU0 : (fun y=>U (a.2.1,y))=
      (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) := rfl
  rw [hP,hU0] at hComm
  exact hComm.trans (by ring)

theorem hasDerivAt_vectorProfileCellPotentialFirstVariation_time (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    (a : VectorProfileCellParameter n) (hq : a.1<s₀.q (i+1))
    (hθ : a.2.1∈Ioo (0:ℝ) 1) (x : Field n) :
    HasDerivAt (fun q=>vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,a.2) x)
      (-((1-t)*β^2)/2*(
        vectorLaplacian (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x+
        2*vectorProfileMass s₀ s₁ a.2.1 i*
          inner ℝ (gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x)
            (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x)+
        (s₁.m i-s₀.m i)*‖gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x‖^2)) a.1 := by
  have hP : ContDiffAt ℝ ∞ (fun q=>vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,a.2) x) a.1 :=
    ContDiffAt.comp (f := fun q : ℝ=>((q,a.2),x))
      (g := fun z : VectorProfileCellParameter n×Field n=>
        vectorProfileCellPotentialFirstVariation s₀ s₁ β t i z.1 z.2) a.1
      (contDiffAt_vectorProfileCellPotentialFirstVariation s₀ s₁ β t hβ ht i hi a hq hθ x)
      (by fun_prop)
  rw [←vectorProfileCellPotentialFirstVariation_time_PDE s₀ s₁ β t hβ ht i hi a hq hθ x]
  exact (hP.differentiableAt (by simp)).hasDerivAt

end QuantitativePaper
