module
public import FourPapersCommon.MovingDerivativeLimit
public import Mathlib.Analysis.Calculus.FDeriv.Extend

@[expose] public section

/-! Passage from genuine finite Gaussian derivatives to the derivative of a
continuous-path expectation. Moving-parameter convergence is used, so no
derivative of the limiting function is assumed. The endpoint theorem obtains
actual one-sided derivatives when Gaussian coordinates degenerate. -/
noncomputable section
open Set Filter
open scoped Topology
namespace HexagonPaper
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_pathHeat_limit (F D : ℕ→ℝ→ℝ) (f d : ℝ→ℝ)
    (a b x : ℝ) (hx : x∈Ioo a b)
    (hD : ∀n y,y∈Ioo a b→HasDerivAt (F n) (D n y) y)
    (hF : ∀y,y∈Ioo a b→Tendsto (fun n=>F n y) atTop (𝓝 (f y)))
    (hlim : ∀y : ℕ→ℝ,Tendsto y atTop (𝓝 x)→
      Tendsto (fun n=>D n (y n)) atTop (𝓝 (d x))) :
    HasDerivAt f (d x) x := by
  have hu := tendsto_prod_filter_iff.mp
    (FourPapersCommon.tendsto_prod_of_all_moving_sequences D x (d x) hlim)
  apply hasDerivAt_of_tendstoUniformlyOnFilter hu
  · exact eventually_prod_iff.mpr ⟨_,Eventually.of_forall (fun _=>True.intro),
      fun y=>y∈Ioo a b,isOpen_Ioo.mem_nhds hx,fun {_} _ {_} hy=>hD _ _ hy⟩
  · exact eventually_of_mem (isOpen_Ioo.mem_nhds hx) (fun y hy=>hF y hy)

theorem pathHeat_endpoint_derivatives (f d : ℝ→ℝ) (a b : ℝ) (hab : a<b)
    (hf : ContinuousOn f (Icc a b)) (hd : ContinuousOn d (Icc a b))
    (hderiv : ∀x,x∈Ioo a b→HasDerivAt f (d x) x) :
    HasDerivWithinAt f (d a) (Ici a) a ∧
      HasDerivWithinAt f (d b) (Iic b) b := by
  have hdiff : DifferentiableOn ℝ f (Ioo a b) :=
    fun x hx=>(hderiv x hx).differentiableAt.differentiableWithinAt
  have hfa : ContinuousWithinAt f (Ioo a b) a :=
    (hf a ⟨le_rfl,hab.le⟩).mono Ioo_subset_Icc_self
  have hfb : ContinuousWithinAt f (Ioo a b) b :=
    (hf b ⟨hab.le,le_rfl⟩).mono Ioo_subset_Icc_self
  have hda : Tendsto d (𝓝[>] a) (𝓝 (d a)) := by
    have h := hd a ⟨le_rfl,hab.le⟩
    rw [ContinuousWithinAt,nhdsWithin_Icc_eq_nhdsGE hab] at h
    exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hdb : Tendsto d (𝓝[<] b) (𝓝 (d b)) := by
    have h := hd b ⟨hab.le,le_rfl⟩
    rw [ContinuousWithinAt,nhdsWithin_Icc_eq_nhdsLE hab] at h
    exact h.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
  have hda' : Tendsto (deriv f) (𝓝[>] a) (𝓝 (d a)) := by
    apply hda.congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    exact (hderiv x hx).deriv.symm
  have hdb' : Tendsto (deriv f) (𝓝[<] b) (𝓝 (d b)) := by
    apply hdb.congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    exact (hderiv x hx).deriv.symm
  exact ⟨hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hfa (Ioo_mem_nhdsGT hab) hda',
    hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hfb (Ioo_mem_nhdsLT hab) hdb'⟩

end HexagonPaper
