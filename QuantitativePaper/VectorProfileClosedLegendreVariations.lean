module
public import QuantitativePaper.VectorProfileClosedObservables
public import QuantitativePaper.VectorProfileVariationEndpoints

@[expose] public section

/-! Actual profile differentiation of the chosen inverse and stationary
value at every closed overlap-cell point, including zero variance. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem contDiffAt_vectorProfileCell_fixed_time_potential
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (q : ℝ) (hq : q∈Icc (s₀.q i) (s₀.q (i+1)))
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Ioo (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (fun w : VectorProfileParameter n×Field n=>
      vectorProfileCellJointPotential s₀ s₁ β t i ((q,w.1),w.2)) z := by
  have hf:=retainedJetExponentialOn_vectorProfileCellJointPotential (n:=n)
    s₀ s₁ β t ht i hi (z.1.1/2) ((z.1.1+1)/2) (by linarith [hθ.1]) (by linarith [hθ.2])
  exact hf.smooth q hq z ⟨by linarith [hθ.1],by linarith [hθ.2]⟩

theorem contDiffAt_vectorProfileCell_fixed_time_inverse_curve
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (q θ : ℝ)
    (hθ : θ∈Ioo (0:ℝ) 1) (p : Couplings n×ℝ) (m : Field n)
    (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun α=>vectorProfileCellLegendreField s₀ s₁ β t i ((q,α,p),m)) θ :=
  ContDiffAt.comp (f:=fun α : ℝ=>((α,p),m))
    (g:=fun z : VectorProfileParameter n×Field n=>vectorProfileLegendreField
      s₀ s₁ β t (vectorProfileCellOverlap q) (k+2) z.1.1 z.1.2 z.2) θ
    (contDiffAt_vectorProfileLegendreField_joint s₀ s₁ β t ht
      (vectorProfileCellOverlap q) (k+2) le_rfl (θ,p) hθ m hm) (by fun_prop)

theorem vectorProfileRetainedSecondVariation_eq_field_closed
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1)
    (i : ℕ) (hi : i≤k+1) (q : ℝ) (hq : q∈Icc (s₀.q i) (s₀.q (i+1)))
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Ioo (0:ℝ) 1) :
    vectorProfileRetainedSecondVariation s₀ s₁ β t i q z=
      vectorProfileCellFieldSecondVariation s₀ s₁ β t i ((q,z.1),z.2) := by
  let a : VectorProfileCellParameter n:=(q,z.1)
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,z.2)
  have hm:=vectorProfileCellGradient_mem_openSpinCube s₀ s₁ β t i hi a hq
    ⟨hθ.1.le,hθ.2.le⟩ z.2
  let U : ℝ×Field n→ℝ:=fun w=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,w.1,z.1.2),w.2)
  let Y : ℝ→Field n:=fun α=>vectorProfileCellLegendreField s₀ s₁ β t i ((q,α,z.1.2),m)
  let Φ : ℝ→ℝ:=fun α=>vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i ((q,α,z.1.2),m)
  let W:=vectorProfileJointPotential (n:=n) s₀ s₁ β t (vectorProfileCellOverlap q) (k+2)
  have hU : ContDiffAt ℝ ∞ U (z.1.1,Y z.1.1):=ContDiffAt.comp
    (f:=fun w : ℝ×Field n=>((w.1,z.1.2),w.2))
    (g:=fun w : VectorProfileParameter n×Field n=>
      vectorProfileCellJointPotential s₀ s₁ β t i ((q,w.1),w.2)) (z.1.1,Y z.1.1)
    (contDiffAt_vectorProfileCell_fixed_time_potential s₀ s₁ β t ht i hi q hq
      ((z.1.1,z.1.2),Y z.1.1) hθ) (by fun_prop)
  have hY:=contDiffAt_vectorProfileCell_fixed_time_inverse_curve s₀ s₁ β t ht i q z.1.1
    hθ z.1.2 m hm
  have hStationary : (fun α=>gradient (fun x=>U (α,x)) (Y α))=ᶠ[𝓝 z.1.1](fun _=>m):=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with α hα
    change vectorProfileCellJointGradient s₀ s₁ β t i ((q,α,z.1.2),Y α)=m
    rw [vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t i hi (q,α,z.1.2) hq
      ⟨hα.1.le,hα.2.le⟩]
    exact vectorMagnetization_legendreField _ β t z.1.2 (k+2) m hm
  have hUnit : IsUnit (hessianOperator (fun x=>U (z.1.1,x)) (Y z.1.1)):=by
    change IsUnit (hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i (a,x)) (Y z.1.1))
    rw [vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi a hq ⟨hθ.1.le,hθ.2.le⟩]
    exact vectorFieldHessian_isUnit _ β t z.1.2 (k+2) _
  have hFirst : ∀ᶠα in 𝓝 z.1.1,HasDerivAt Φ (-β⁻¹*deriv (fun τ=>U (τ,Y α)) α) α:=by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with α hα
    have hLine : HasDerivAt (fun τ : ℝ=>(τ,z.1.2)) (1,0) α:=
      (hasDerivAt_id α).prodMk (hasDerivAt_const α z.1.2)
    have hEnv:=(hasFDerivAt_vectorProfileLegendrePotential_parameter s₀ s₁ β t ht
      (vectorProfileCellOverlap q) (k+2) le_rfl (α,z.1.2) hα m hm).comp_hasDerivAt α hLine |>.div_const β
    have hRaw:=((contDiffAt_vectorProfileJointPotential s₀ s₁ β t ht
      (vectorProfileCellOverlap q) (k+2) le_rfl ((α,z.1.2),Y α) hα).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt α (hLine.prodMk (hasDerivAt_const α (Y α)))
    have he : (fun τ=>W ((τ,z.1.2),Y α))=ᶠ[𝓝 α](fun τ=>U (τ,Y α)):=by
      filter_upwards [isOpen_Ioo.mem_nhds hα] with τ hτ
      have hf:=congrFun (vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi
        (q,τ,z.1.2) hq ⟨hτ.1.le,hτ.2.le⟩) (Y α)
      have hg:=congrFun (vectorProfileJointPotential_eq_inverseScheme s₀ s₁ β t
        (vectorProfileCellOverlap q) (k+2) le_rfl τ ⟨hτ.1.le,hτ.2.le⟩ z.1.2) (Y α)
      exact hg.trans hf.symm
    have hd : deriv (fun τ=>U (τ,Y α)) α=
        (fderiv ℝ W ((α,z.1.2),Y α)) ((1,0),0):=he.deriv_eq.symm.trans hRaw.deriv
    apply hEnv.congr_deriv
    change -(fderiv ℝ W ((α,z.1.2),Y α) ((1,0),0))/β= -β⁻¹*deriv (fun τ=>U (τ,Y α)) α
    rw [hd]
    ring
  have hs:=stationary_second_variation U Y Φ z.1.1 β⁻¹ m hU
    (hY.differentiableAt (by simp)) hStationary hUnit hFirst
  have hY0 : Y z.1.1=z.2:=vectorProfileCellLegendreField_gradient s₀ s₁ β t i hi a hq
    ⟨hθ.1.le,hθ.2.le⟩ z.2
  rw [hY0] at hs
  exact hs.symm

end QuantitativePaper
