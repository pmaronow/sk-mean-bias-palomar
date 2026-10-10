module
public import Mathlib.MeasureTheory.Measure.AEDisjoint
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Bases

@[expose] public section

/-! A common null set for continuous parameterized order inequalities:
countably many dense tests suffice. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace FourPapersCommon
variable {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [SeparableSpace E]

theorem ae_all_continuous_le (P : Measure Ω) (F G : Ω→E→ℝ)
    (hF : ∀ω,Continuous (F ω)) (hG : ∀ω,Continuous (G ω))
    (h : ∀x,∀ᵐω ∂P,F ω x≤G ω x) : ∀ᵐω ∂P,∀x,F ω x≤G ω x := by
  obtain ⟨D,hDc,hDd⟩:=TopologicalSpace.exists_countable_dense E
  letI : Countable D:=hDc.to_subtype
  have hDa : ∀ᵐω ∂P,∀x : D,F ω x≤G ω x:=ae_all_iff.mpr fun x=>h x
  filter_upwards [hDa] with ω hω
  intro x
  have hsub : D⊆{y|F ω y≤G ω y}:=fun y hy=>hω ⟨y,hy⟩
  exact closure_minimal hsub (isClosed_le (hF ω) (hG ω)) (hDd x)

end FourPapersCommon
