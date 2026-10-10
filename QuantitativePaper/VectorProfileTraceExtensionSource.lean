module
public import QuantitativePaper.VectorProfileResponseJumps
public import QuantitativePaper.VectorProfileTraceTimeGrowth
public import QuantitativePaper.VectorProfileFieldSourceValues

@[expose] public section

/-! The closed-cell reaction extension agrees with the genuine time
derivative on the open cell. Its spatial generator and exponential bounds
therefore follow from the actual trace-time equation, without assigning a
two-sided derivative to a profile atom. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileCellFieldGenerator_congr
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (F G : VectorProfileCellParameter n×Field n→ℝ)
    (a : VectorProfileCellParameter n) (x : Field n)
    (he : F=ᶠ[𝓝 (a,x)]G) :
    vectorProfileCellFieldGenerator s₀ s₁ β t i F a x=
      vectorProfileCellFieldGenerator s₀ s₁ β t i G a x := by
  have hTime : (fun q=>F ((q,a.2),x))=ᶠ[𝓝 a.1](fun q=>G ((q,a.2),x)):=
    he.comp_tendsto ((show ContinuousAt (fun q : ℝ=>((q,a.2),x)) a.1 by fun_prop).tendsto)
  have hSpace : (fun y=>F (a,y))=ᶠ[𝓝 x](fun y=>G (a,y)):=
    he.comp_tendsto ((show ContinuousAt (fun y : Field n=>(a,y)) x by fun_prop).tendsto)
  unfold vectorProfileCellFieldGenerator
  rw [hTime.deriv_eq,hSpace.fderiv_eq,(hSpace.fderiv (𝕜:=ℝ)).fderiv_eq]

theorem vectorProfileCellFieldTraceTimeExtension_eq_time
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0:ℝ) 1)
    (x : Field n) :
    vectorProfileCellFieldTraceTimeExtension s₀ s₁ β t i (a,x)=
      vectorProfileCellFieldTraceTime s₀ s₁ β t i (a,x) := by
  exact vectorProfileCellTraceTimeExtension_eq_time s₀ s₁ β t hβ ht i hi a hq hθ _
    (vectorProfileCellGradient_mem_openSpinCube s₀ s₁ β t i hi a
      ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ x)

theorem vectorProfileCellFieldTraceTimeExtension_eventually_eq_time
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0:ℝ) 1)
    (x : Field n) :
    vectorProfileCellFieldTraceTimeExtension s₀ s₁ β t i=ᶠ[𝓝 (a,x)]
      vectorProfileCellFieldTraceTime s₀ s₁ β t i := by
  have hU:=isOpen_vectorProfileJointCylinder (n:=n) (s₀.q i) (s₀.q (i+1)) 0 1
  filter_upwards [hU.mem_nhds ⟨hq,hθ⟩] with z hz
  exact vectorProfileCellFieldTraceTimeExtension_eq_time s₀ s₁ β t hβ ht i hi z.1
    hz.1 hz.2 z.2

theorem exponentialSmoothOn_vectorProfileCellFieldTraceTimeExtension (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (l u A B : ℝ)
    (hl : s₀.q i≤l) (hu : u<s₀.q (i+1)) (hA : 0<A) (hB : B<1) :
    ExponentialSmoothOn (vectorProfileCellFieldTraceTimeExtension (n:=n) s₀ s₁ β t i)
      (vectorProfileJointCylinder l u A B) := by
  apply (exponentialSmoothOn_vectorProfileCellFieldTraceTime hn s₀ s₁ β t hβ ht i hi
    l u A B hl hu hA hB).congr
  intro z hz
  exact (vectorProfileCellFieldTraceTimeExtension_eventually_eq_time s₀ s₁ β t hβ ht
    i hi z.1 ⟨hl.trans_lt hz.1.1,hz.1.2.trans hu⟩
    ⟨hA.trans hz.2.1,hz.2.2.trans hB⟩ z.2).symm

theorem vectorProfileCellFieldTraceTimeExtension_generator
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0:ℝ) 1)
    (x : Field n) :
    vectorProfileCellFieldGenerator s₀ s₁ β t i
      (vectorProfileCellFieldTraceTimeExtension s₀ s₁ β t i) a x=
      vectorProfileFieldTraceTimeSource s₀ s₁ β t i (a,x) := by
  rw [vectorProfileCellFieldGenerator_congr s₀ s₁ β t i _ _ a x
    (vectorProfileCellFieldTraceTimeExtension_eventually_eq_time s₀ s₁ β t hβ.ne' ht
      i hi a hq hθ x)]
  exact vectorProfileCellFieldTraceTime_generator s₀ s₁ β t hβ ht i hi a hq hθ x

end QuantitativePaper
