module
public import QuantitativePaper.VectorProfileTimePullbacks

@[expose] public section

/-! The actual fixed-magnetization trace time derivative in original
field coordinates. The inverse curve is differentiated, not held fixed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem contDiffAt_vectorProfileCellRawTrace
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1<s₀.q (i+1)) (hθ : a.2.1∈Ioo (0 : ℝ) 1) (x : Field n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellRawTrace s₀ s₁ β t i z.1 z.2) (a,x) := by
  have hU:=contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi (a,x) hq hθ
  have hH:=contDiffAt_partial_hessian (vectorProfileCellJointPotential s₀ s₁ β t i) (a,x) hU
  exact euclideanOperatorTraceCLM.contDiff.contDiffAt.comp (a,x) hH

theorem vectorProfileCellFieldTraceTime_formula
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0 : ℝ) 1) (x : Field n) :
    vectorProfileCellFieldTraceTime s₀ s₁ β t i (a,x)=
      β*(deriv (fun q=>vectorProfileCellRawTrace s₀ s₁ β t i (q,a.2) x) a.1-
        fderiv ℝ (vectorProfileCellRawTrace s₀ s₁ β t i a) x
          ((Ring.inverse (hessianOperator
            (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x))
            (gradient (vectorProfileCellPotentialTime s₀ s₁ β t i a) x))) := by
  let m:=vectorProfileCellJointGradient s₀ s₁ β t i (a,x)
  let Y : ℝ→Field n:=fun q=>vectorProfileCellLegendreField s₀ s₁ β t i ((q,a.2),m)
  let W : ℝ×Field n→ℝ:=fun z=>vectorProfileCellRawTrace s₀ s₁ β t i (z.1,a.2) z.2
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
      vectorProfileCellRawTrace s₀ s₁ β t i z.1 z.2) (a.1,Y a.1)
    (contDiffAt_vectorProfileCellRawTrace s₀ s₁ β t hβ ht i hi a hq.2 hθ (Y a.1))
    (by fun_prop)
  have he : (fun q=>vectorProfileCellTrace s₀ s₁ β t i (q,a.2) m)=ᶠ[𝓝 a.1]
      (fun q=>β*W (q,Y q)):=by
    filter_upwards [isOpen_Ioo.mem_nhds hq] with q hq'
    unfold vectorProfileCellTrace
    rw [vectorProfileCellPhysicalHessian_eq s₀ s₁ β t hβ i (q,a.2) m hm]
    have heU : (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,a.2),y))=
        vectorRecursion (vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap q) a.2.1)
          β t a.2.2 (k+2):=vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi (q,a.2)
            ⟨hq'.1.le,hq'.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩
    dsimp only [W,vectorProfileCellRawTrace,Y]
    rw [heU]
    simp only [euclideanOperatorTrace,euclideanOperatorMatrix_smul,Matrix.trace_smul,smul_eq_mul]
    rfl
  have hd:=deriv_time_curve_composition W Y a.1 (hW.of_le (by norm_num)) (hY.of_le (by norm_num))
  have hdY:=(hasDerivAt_vectorProfileCellLegendreField_time s₀ s₁ β t hβ ht i hi a hq hθ m hm).deriv
  unfold vectorProfileCellFieldTraceTime vectorProfileCellTraceTime
  rw [he.deriv_eq,deriv_const_mul_field,hd,hdY,hY0]
  have hy : vectorProfileCellLegendreField s₀ s₁ β t i (a,m)=x:=hY0
  rw [hy]
  simp only [map_neg,←sub_eq_add_neg]
  rfl

end QuantitativePaper
