module
public import FourPapersCommon.EvenRadialTransform
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section

/-! Genuine closed-half-line smoothness from a locally smooth even signed
amplitude. A symmetric compact bump supplies the full-line extension used
by the radial differentiation theorem. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 400000

theorem contDiffOn_evenRadialTransform_local (f : ℝ→ℝ) (R : ℝ) (hR : 1<R)
    (hf : ContDiffOn ℝ ∞ f (Ioo (-R) R)) (he : ∀x∈Ioo (-R) R,f (-x)=f x) :
    ContDiffOn ℝ ∞ (fun u=>f (Real.sqrt u)) (Icc (0:ℝ) 1) := by
  let η : ContDiffBump (0:ℝ):=⟨1,(1+R)/2,zero_lt_one,by linarith⟩
  let g : ℝ→ℝ:=fun x=>η x*f x
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x∈Ioo (-R) R
    · exact η.contDiff.contDiffAt.mul (hf.contDiffAt (isOpen_Ioo.mem_nhds hx))
    · have hnot : x∉tsupport (η:ℝ→ℝ) := by
        rw [η.tsupport_eq]
        intro hm
        have hn : |x|≤(1+R)/2:=by simpa only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,η] using hm
        have hh:=abs_le.mp hn
        exact hx ⟨by linarith,by linarith⟩
      have hz : g=ᶠ[𝓝 x](fun _=>0) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
        change η y*f y=0
        change η y=0 at hy
        rw [hy,zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  have hge (x:ℝ) : g (-x)=g x:=by
    dsimp only [g]
    rw [η.neg]
    by_cases hx:x∈Ioo (-R) R
    · rw [he x hx]
    · have hn : (1+R)/2≤|x| := by
        by_contra hh
        have hh' := abs_lt.mp (lt_of_not_ge hh)
        exact hx ⟨by linarith,by linarith⟩
      rw [η.zero_of_le_dist (by simpa only [dist_zero_right,Real.norm_eq_abs,η] using hn)]
      simp
  have hc:=(contDiffOn_evenRadialTransform g hg hge).mono
    (show Icc (0:ℝ) 1⊆Ici 0 from fun _ h=>h.1)
  apply hc.congr
  intro u hu
  change f (Real.sqrt u)=η (Real.sqrt u)*f (Real.sqrt u)
  rw [η.one_of_mem_closedBall,one_mul]
  simpa only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),η]
    using Real.sqrt_le_one.mpr hu.2

end FourPapersCommon
