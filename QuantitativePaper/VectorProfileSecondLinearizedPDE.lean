module
public import QuantitativePaper.VectorProfileLinearizedPDE

@[expose] public section

/-! The actual second profile variation satisfies the literal twice
linearized finite-cell PDE. Its reaction source is expressed only in the
actual first profile gradient and the actual field gradient. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem contDiffAt_vectorProfileCellPotentialSecondVariation
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (a : VectorProfileCellParameter n)
    (hq : a.1<s₀.q (i+1)) (hθ : a.2.1∈Ioo (0:ℝ) 1) (x : Field n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPotentialSecondVariation s₀ s₁ β t i z.1 z.2) (a,x) := by
  let P : ℝ×(ℝ×((Couplings n×ℝ)×Field n))→ℝ:=fun z=>
    vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (z.2.1,z.1,z.2.2.1) z.2.2.2
  have hP : ContDiffAt ℝ ∞ P (a.2.1,a.1,a.2.2,x):=ContDiffAt.comp
    (f := fun z : ℝ×(ℝ×((Couplings n×ℝ)×Field n))=>((z.2.1,z.1,z.2.2.1),z.2.2.2))
    (g := fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPotentialFirstVariation s₀ s₁ β t i z.1 z.2) (a.2.1,a.1,a.2.2,x)
    (contDiffAt_vectorProfileCellPotentialFirstVariation s₀ s₁ β t hβ ht i hi a hq hθ x)
    (by fun_prop)
  have hd:=contDiffAt_partialParamDerivative (1:ℝ) P (a.2.1,a.1,a.2.2,x) hP
  have hh:=ContDiffAt.comp
    (f := fun z : VectorProfileCellParameter n×Field n=>(z.1.2.1,z.1.1,z.1.2.2,z.2))
    (g := partialParamDerivative (1:ℝ) P) (a,x) hd (by fun_prop)
  simpa only [Function.comp_def,partialParamDerivative,fderiv_apply_one_eq_deriv,P,
    vectorProfileCellPotentialFirstVariation,vectorProfileCellPotentialSecondVariation] using hh

theorem vectorProfileCellPotentialSecondVariation_time_PDE (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    (a : VectorProfileCellParameter n) (hq : a.1<s₀.q (i+1))
    (hθ : a.2.1∈Ioo (0:ℝ) 1) (x : Field n) :
    deriv (fun q=>vectorProfileCellPotentialSecondVariation s₀ s₁ β t i (q,a.2) x) a.1=
      -((1-t)*β^2)/2*(
        vectorLaplacian (vectorProfileCellPotentialSecondVariation s₀ s₁ β t i a) x+
        2*vectorProfileMass s₀ s₁ a.2.1 i*
          inner ℝ (gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x)
            (gradient (vectorProfileCellPotentialSecondVariation s₀ s₁ β t i a) x)+
        2*vectorProfileMass s₀ s₁ a.2.1 i*
          ‖gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x‖^2+
        4*(s₁.m i-s₀.m i)*
          inner ℝ (gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x)
            (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x)) := by
  let U : ℝ×Field n→ℝ:=fun z=>
    vectorProfileCellJointPotential s₀ s₁ β t i ((a.1,z.1,a.2.2),z.2)
  let P : ℝ×Field n→ℝ:=fun z=>
    vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (a.1,z.1,a.2.2) z.2
  have hU : ContDiffAt ℝ ∞ U (a.2.1,x):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((a.1,z.1,a.2.2),z.2))
    (g := vectorProfileCellJointPotential s₀ s₁ β t i) (a.2.1,x)
    (contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi (a,x) hq hθ)
    (by fun_prop)
  have hP : ContDiffAt ℝ ∞ P (a.2.1,x):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((a.1,z.1,a.2.2),z.2))
    (g := fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPotentialFirstVariation s₀ s₁ β t i z.1 z.2) (a.2.1,x)
    (contDiffAt_vectorProfileCellPotentialFirstVariation s₀ s₁ β t hβ ht i hi a hq hθ x)
    (by fun_prop)
  have hG:=hasDerivAt_partial_gradient U a.2.1 x hU
  have hGP:=hasDerivAt_partial_gradient P a.2.1 x hP
  have hLap:=hasDerivAt_vectorLaplacian_parameter P a.2.1 x hP
  have hInner:=(hG.inner ℝ hGP)
  have hSq:=(hG.inner ℝ hG)
  simp only [real_inner_self_eq_norm_sq] at hSq
  have hMass : HasDerivAt (fun θ=>vectorProfileMass s₀ s₁ θ i) (s₁.m i-s₀.m i) a.2.1 := by
    unfold vectorProfileMass
    convert ((hasDerivAt_const a.2.1 1).sub (hasDerivAt_id a.2.1)).mul_const (s₀.m i) |>.add
      ((hasDerivAt_id a.2.1).mul_const (s₁.m i)) using 1
    · ext θ
      simp only [Pi.add_apply,Pi.sub_apply,id_eq]
    · ring
  have hR:=(hLap.add ((hMass.mul hInner).const_mul 2) |>.add
    (hSq.const_mul (s₁.m i-s₀.m i))).const_mul (-((1-t)*β^2)/2)
  simp only [Pi.add_apply,Pi.mul_apply] at hR
  simp only [←mul_assoc] at hR
  let V : ℝ×ℝ→ℝ:=fun z=>vectorProfileCellJointPotential s₀ s₁ β t i ((z.1,z.2,a.2.2),x)
  have hV : ContDiffAt ℝ ∞ V (a.1,a.2.1):=ContDiffAt.comp
    (f := fun z : ℝ×ℝ=>((z.1,z.2,a.2.2),x))
    (g := vectorProfileCellJointPotential s₀ s₁ β t i) (a.1,a.2.1)
    (contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi (a,x) hq hθ)
    (by fun_prop)
  have hEq : (fun θ=>deriv (fun q=>deriv (fun α=>V (q,α)) θ) a.1)=ᶠ[𝓝 a.2.1]
      (fun θ=>-((1-t)*β^2)/2*(vectorLaplacian (fun y=>P (θ,y)) x+
        2*vectorProfileMass s₀ s₁ θ i*inner ℝ (gradient (fun y=>U (θ,y)) x)
          (gradient (fun y=>P (θ,y)) x)+
        (s₁.m i-s₀.m i)*‖gradient (fun y=>U (θ,y)) x‖^2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ hθ'
    exact vectorProfileCellPotentialFirstVariation_time_PDE s₀ s₁ β t hβ ht i hi
      (a.1,θ,a.2.2) hq hθ' x
  have hComm:=deriv_real_parameters_commute_third V a.1 a.2.1 hV
  have hSwap (θ : ℝ) (hθ' : θ∈Ioo (0:ℝ) 1) :
      deriv (fun r=>deriv (fun α=>V (r,α)) θ) a.1=
        deriv (fun α=>deriv (fun r=>V (r,α)) a.1) θ :=
    deriv_real_parameters_commute V a.1 θ (ContDiffAt.comp
      (f := fun z : ℝ×ℝ=>((z.1,z.2,a.2.2),x))
      (g := vectorProfileCellJointPotential s₀ s₁ β t i) (a.1,θ)
      (contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi ((a.1,θ,a.2.2),x) hq hθ')
      (by fun_prop))
  have hSwapEq : (fun θ=>deriv (fun r=>deriv (fun α=>V (r,α)) θ) a.1)=ᶠ[𝓝 a.2.1]
      (fun θ=>deriv (fun α=>deriv (fun r=>V (r,α)) a.1) θ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ hθ'
    exact hSwap θ hθ'
  rw [←hSwapEq.deriv_eq,hEq.deriv_eq,hR.deriv] at hComm
  have hP0 : (fun y=>P (a.2.1,y))=vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a := rfl
  have hQ : (fun y=>deriv (fun θ=>P (θ,y)) a.2.1)=
      vectorProfileCellPotentialSecondVariation s₀ s₁ β t i a := rfl
  have hUP : (fun y=>deriv (fun θ=>U (θ,y)) a.2.1)=
      vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a := rfl
  have hU0 : (fun y=>U (a.2.1,y))=
      (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) := rfl
  rw [hP0,hQ,hUP,hU0] at hComm
  change deriv (fun q=>vectorProfileCellPotentialSecondVariation s₀ s₁ β t i (q,a.2) x) a.1=_ at hComm
  rw [real_inner_self_eq_norm_sq] at hComm
  exact hComm.trans (by rw [real_inner_comm
    (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x)
    (gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x)];ring)

theorem hasDerivAt_vectorProfileCellPotentialSecondVariation_time (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    (a : VectorProfileCellParameter n) (hq : a.1<s₀.q (i+1))
    (hθ : a.2.1∈Ioo (0:ℝ) 1) (x : Field n) :
    HasDerivAt (fun q=>vectorProfileCellPotentialSecondVariation s₀ s₁ β t i (q,a.2) x)
      (-((1-t)*β^2)/2*(
        vectorLaplacian (vectorProfileCellPotentialSecondVariation s₀ s₁ β t i a) x+
        2*vectorProfileMass s₀ s₁ a.2.1 i*
          inner ℝ (gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x)
            (gradient (vectorProfileCellPotentialSecondVariation s₀ s₁ β t i a) x)+
        2*vectorProfileMass s₀ s₁ a.2.1 i*
          ‖gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x‖^2+
        4*(s₁.m i-s₀.m i)*
          inner ℝ (gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x)
            (gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x))) a.1 := by
  have hQ : ContDiffAt ℝ ∞ (fun q=>vectorProfileCellPotentialSecondVariation s₀ s₁ β t i (q,a.2) x) a.1:=
    ContDiffAt.comp (f := fun q : ℝ=>((q,a.2),x))
      (g := fun z : VectorProfileCellParameter n×Field n=>
        vectorProfileCellPotentialSecondVariation s₀ s₁ β t i z.1 z.2) a.1
      (contDiffAt_vectorProfileCellPotentialSecondVariation s₀ s₁ β t hβ ht i hi a hq hθ x)
      (by fun_prop)
  rw [←vectorProfileCellPotentialSecondVariation_time_PDE s₀ s₁ β t hβ ht i hi a hq hθ x]
  exact (hQ.differentiableAt (by simp)).hasDerivAt

end QuantitativePaper
