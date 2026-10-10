module
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

@[expose] public section

/-! A genuine derivative-limit criterion from convergence at every moving
parameter sequence. No derivative of the limiting function is assumed. -/
noncomputable section
open Set Filter Function
open scoped Topology
namespace FourPapersCommon

theorem tendsto_extend_strictMono {u : ℕ→ℕ} (hu : StrictMono u)
    {x : ℕ→ℝ} {b : ℝ} (hx : Tendsto x atTop (𝓝 b)) :
    Tendsto (Function.extend u x (fun _=>b)) atTop (𝓝 b) := by
  classical
  rw [Metric.tendsto_atTop] at hx ⊢
  intro ε hε
  obtain ⟨N,hN⟩:=hx ε hε
  refine ⟨u N,fun n hn=>?_⟩
  by_cases h : ∃j,u j=n
  · obtain ⟨j,rfl⟩:=h
    rw [hu.injective.extend_apply]
    exact hN j (hu.le_iff_le.mp hn)
  · rw [Function.extend_apply' _ _ _ h]
    simpa using hε

theorem tendsto_prod_of_all_moving_sequences (F : ℕ→ℝ→ℝ) (b d : ℝ)
    (h : ∀x : ℕ→ℝ,Tendsto x atTop (𝓝 b)→Tendsto (fun j=>F j (x j)) atTop (𝓝 d)) :
    Tendsto (fun z : ℕ×ℝ=>F z.1 z.2) (atTop×ˢ𝓝 b) (𝓝 d) := by
  apply tendsto_of_subseq_tendsto
  intro z hz
  have hn : Tendsto (fun j=>(z j).1) atTop atTop:=tendsto_fst.comp hz
  obtain ⟨φ,hφ,hnφ⟩:=strictMono_subseq_of_tendsto_atTop hn
  let u:=fun j=>(z (φ j)).1
  let x:=fun j=>(z (φ j)).2
  have hu : StrictMono u:=hnφ
  have hx : Tendsto x atTop (𝓝 b):=(tendsto_snd.comp hz).comp hφ.tendsto_atTop
  have he:=h (Function.extend u x (fun _=>b)) (tendsto_extend_strictMono hu hx)
  refine ⟨φ,?_⟩
  have hh:=he.comp hu.tendsto_atTop
  simpa only [Function.comp_def,hu.injective.extend_apply,u,x] using hh

theorem hasDerivAt_of_all_moving_derivatives (F D : ℕ→ℝ→ℝ) (f : ℝ→ℝ)
    (b d : ℝ) (hb : 0<b)
    (hD : ∀j x,0<x→HasDerivAt (F j) (D j x) x)
    (hF : ∀x,0<x→Tendsto (fun j=>F j x) atTop (𝓝 (f x)))
    (hlim : ∀x : ℕ→ℝ,Tendsto x atTop (𝓝 b)→Tendsto (fun j=>D j (x j)) atTop (𝓝 d)) :
    HasDerivAt f d b := by
  have hu := tendsto_prod_filter_iff.mp (tendsto_prod_of_all_moving_sequences D b d hlim)
  apply hasDerivAt_of_tendstoUniformlyOnFilter hu
  · exact eventually_prod_iff.mpr ⟨_,Eventually.of_forall (fun j=>True.intro),
      fun x=>0<x,Ioi_mem_nhds hb,fun {_} _ {_} hx=>hD _ _ hx⟩
  · exact eventually_of_mem (Ioi_mem_nhds hb) (fun x hx=>hF x hx)

end FourPapersCommon
