module
public import QuantitativePaper.VectorProfileLegendreTimeCurve
public import FourPapersCommon.TimeCurveComposition

@[expose] public section

/-! Actual fixed-magnetization time variations expressed in original
field coordinates. These expressions make exponential growth checkable
from the literal raw Gaussian profile jets and Hessian inverse bound. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfileCellPotentialTime (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (x : Field n) : ℝ:=
  deriv (fun q=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,a.2),x)) a.1

def vectorProfileCellRawTrace (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (x : Field n) : ℝ:=
  euclideanOperatorTrace (hessianOperator
    (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x)

theorem contDiffAt_vectorProfileCellPotentialFirstVariation
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1<s₀.q (i+1)) (hθ : a.2.1∈Ioo (0 : ℝ) 1) (x : Field n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPotentialFirstVariation s₀ s₁ β t i z.1 z.2) (a,x) := by
  let U : ℝ×(ℝ×((Couplings n×ℝ)×Field n))→ℝ:=fun z=>
    vectorProfileCellJointPotential s₀ s₁ β t i ((z.2.1,z.1,z.2.2.1),z.2.2.2)
  have hU : ContDiffAt ℝ ∞ U (a.2.1,a.1,a.2.2,x):=ContDiffAt.comp
    (f := fun z : ℝ×(ℝ×((Couplings n×ℝ)×Field n))=>((z.2.1,z.1,z.2.2.1),z.2.2.2))
    (g := vectorProfileCellJointPotential s₀ s₁ β t i) (a.2.1,a.1,a.2.2,x)
    (contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi (a,x) hq hθ)
    (by fun_prop)
  have hd:=contDiffAt_partialParamDerivative (1 : ℝ) U (a.2.1,a.1,a.2.2,x) hU
  have hh:=ContDiffAt.comp
    (f := fun z : VectorProfileCellParameter n×Field n=>(z.1.2.1,z.1.1,z.1.2.2,z.2))
    (g := partialParamDerivative (1 : ℝ) U) (a,x) hd (by fun_prop)
  simpa only [Function.comp_def,partialParamDerivative,fderiv_apply_one_eq_deriv,U,
    vectorProfileCellPotentialFirstVariation] using hh

theorem vectorProfileCellFieldCurvaturePairing_formula
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0 : ℝ) 1) (x : Field n) :
    vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i (a,x)=
      2/((1-t)*β)*(deriv (fun q=>vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,a.2) x) a.1-
        fderiv ℝ (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x
          ((Ring.inverse (hessianOperator
            (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x))
            (gradient (vectorProfileCellPotentialTime s₀ s₁ β t i a) x)))+
        (β*(s₁.m i-s₀.m i))*‖vectorProfileCellJointGradient s₀ s₁ β t i (a,x)‖^2 := by
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
  let Y : ℝ→Field n:=fun q=>vectorProfileCellLegendreField s₀ s₁ β t i ((q,a.2),m)
  let W : ℝ×Field n→ℝ:=fun z=>vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (z.1,a.2) z.2
  have hm:=vectorProfileCellGradient_mem_openSpinCube s₀ s₁ β t i hi a
    ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ x
  have hY0 : Y a.1=x:=vectorProfileCellLegendreField_gradient s₀ s₁ β t i hi a
    ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ x
  have hY : ContDiffAt ℝ ∞ Y a.1:=ContDiffAt.comp
    (f := fun q : ℝ=>((q,a.2),m)) (g := vectorProfileCellLegendreField s₀ s₁ β t i) a.1
    (contDiffAt_vectorProfileCellLegendreField s₀ s₁ β t hβ ht i hi a hq hθ m hm)
    (by fun_prop)
  have hW : ContDiffAt ℝ ∞ W (a.1,Y a.1):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((z.1,a.2),z.2))
    (g := fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPotentialFirstVariation s₀ s₁ β t i z.1 z.2) (a.1,Y a.1)
    (contDiffAt_vectorProfileCellPotentialFirstVariation s₀ s₁ β t hβ ht i hi a hq.2 hθ (Y a.1))
    (by fun_prop)
  have he : (fun q=>vectorProfileCellFirstVariation s₀ s₁ β t i (q,a.2) m)=ᶠ[𝓝 a.1]
      (fun q=>-β⁻¹*W (q,Y q)):=by
    filter_upwards [isOpen_Ioo.mem_nhds hq] with q hq'
    exact vectorProfileCellFirstVariation_field_formula s₀ s₁ β t hβ ht i hi (q,a.2) hq' hθ m hm
  have hd:=deriv_time_curve_composition W Y a.1 (hW.of_le (by norm_num)) (hY.of_le (by norm_num))
  have hdY:=(hasDerivAt_vectorProfileCellLegendreField_time s₀ s₁ β t hβ ht i hi a hq hθ m hm).deriv
  have hh:=vectorProfileCellFirstVariation_time s₀ s₁ β t hβ ht i hi a hq hθ m hm
  rw [he.deriv_eq,deriv_const_mul_field,hd,hdY,hY0] at hh
  have hy : vectorProfileCellLegendreField s₀ s₁ β t i (a,m)=x:=hY0
  rw [hy] at hh
  simp only [map_neg,←sub_eq_add_neg] at hh
  change -β⁻¹*(deriv (fun q=>vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,a.2) x) a.1-
    fderiv ℝ (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i a) x
      ((Ring.inverse (hessianOperator (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x))
        (gradient (vectorProfileCellPotentialTime s₀ s₁ β t i a) x)))=
    -(1-t)/2*vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i (a,x)+
      (1-t)*(β*(s₁.m i-s₀.m i))/2*‖m‖^2 at hh
  have hr : 1-t≠0:=(sub_pos.mpr ht).ne'
  field_simp [hβ] at hh
  field_simp [hβ,hr]
  nlinarith [hh]

end QuantitativePaper
