module
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Tactic

@[expose] public section

/-! Recovering the parameter derivative of a spatial derivative from genuine
one-dimensional partial derivatives. The proof differentiates the parameter
FTC identity under its finite integral; no mixed derivative or response
identity is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000

private theorem parameter_uIcc_subset {l r a b : ℝ}
    (ha : a∈Ioo l r) (hb : b∈Ioo l r) : uIcc a b ⊆ Ioo l r := by
  intro u hu
  rcases mem_uIcc.mp hu with h | h
  · exact ⟨ha.1.trans_le h.1,h.2.trans_lt hb.2⟩
  · exact ⟨hb.1.trans_le h.1,h.2.trans_lt ha.2⟩

/-- Finite parameter increments of the actual spatial derivative equal the
integral of the spatial derivative of the actual parameter partial. -/
theorem spatialDerivative_increment_eq_parameter_integral
    (F P D E : ℝ→ℝ→ℝ) (l r a b x B : ℝ)
    (ha : a∈Ioo l r) (hb : b∈Ioo l r)
    (hD : ContinuousOn (Function.uncurry D) (Ioo l r×ˢuniv))
    (hE : ContinuousOn (Function.uncurry E) (Ioo l r×ˢuniv))
    (hFt : ∀u∈Ioo l r,∀y,HasDerivAt (fun v=>F v y) (D u y) u)
    (hFx : ∀u∈Ioo l r,∀y,HasDerivAt (F u) (P u y) y)
    (hDx : ∀u∈Ioo l r,∀y,HasDerivAt (D u) (E u y) y)
    (hEb : ∀u∈Ioo l r,∀y,‖E u y‖≤B) :
    P b x-P a x=∫u in a..b,E u x := by
  have hs := parameter_uIcc_subset ha hb
  have hDc (y : ℝ) : ContinuousOn (fun u=>D u y) (uIcc a b) :=
    hD.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu=>⟨hs hu,mem_univ y⟩)
  have hEc (y : ℝ) : ContinuousOn (fun u=>E u y) (uIcc a b) :=
    hE.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu=>⟨hs hu,mem_univ y⟩)
  have hv (y : ℝ) : (∫u in a..b,D u y)=F b y-F a y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu=>hFt u (hs hu) y) (hDc y).intervalIntegrable
  have hd : HasDerivAt (fun y=>∫u in a..b,D u y) (∫u in a..b,E u x) x := by
    exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun y u=>D u y) (F' := fun y u=>E u y) (s := univ)
      (bound := fun _=>B) (μ := volume) (a := a) (b := b) (x₀ := x)
      univ_mem
      (.of_forall fun y=>(hDc y).aestronglyMeasurable measurableSet_uIcc |>.mono_set uIoc_subset_uIcc)
      (hDc x).intervalIntegrable
      ((hEc x).aestronglyMeasurable measurableSet_uIcc |>.mono_set uIoc_subset_uIcc)
      (.of_forall fun u hu y _=>hEb u (hs (uIoc_subset_uIcc hu)) y)
      intervalIntegrable_const
      (.of_forall fun u hu y _=>hDx u (hs (uIoc_subset_uIcc hu)) y)).2
  have hf : HasDerivAt (fun y=>∫u in a..b,D u y) (P b x-P a x) x := by
    exact ((hFx b hb x).sub (hFx a ha x)).congr_of_eventuallyEq
      (.of_forall fun y=>hv y)
  exact hf.unique hd

/-- The genuine mixed-partial conclusion, obtained from FTC and dominated
finite-interval differentiation rather than an assumed Schwarz identity. -/
theorem hasDerivAt_spatialDerivative_of_parameterPartials
    (F P D E : ℝ→ℝ→ℝ) (l r a x B : ℝ) (ha : a∈Ioo l r)
    (hD : ContinuousOn (Function.uncurry D) (Ioo l r×ˢuniv))
    (hE : ContinuousOn (Function.uncurry E) (Ioo l r×ˢuniv))
    (hFt : ∀u∈Ioo l r,∀y,HasDerivAt (fun v=>F v y) (D u y) u)
    (hFx : ∀u∈Ioo l r,∀y,HasDerivAt (F u) (P u y) y)
    (hDx : ∀u∈Ioo l r,∀y,HasDerivAt (D u) (E u y) y)
    (hEb : ∀u∈Ioo l r,∀y,‖E u y‖≤B) :
    HasDerivAt (fun u=>P u x) (E a x) a := by
  have hEc : ContinuousOn (fun u=>E u x) (Ioo l r) :=
    hE.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu=>⟨hu,mem_univ x⟩)
  have hc : ContinuousAt (fun u=>E u x) a :=
    (hEc a ha).continuousAt (isOpen_Ioo.mem_nhds ha)
  have hmeas : StronglyMeasurableAtFilter (fun u=>E u x) (𝓝 a) := by
    exact ⟨Ioo l r,isOpen_Ioo.mem_nhds ha,hEc.aestronglyMeasurable measurableSet_Ioo⟩
  have hd := intervalIntegral.integral_hasDerivAt_right
    (show IntervalIntegrable (fun u=>E u x) volume a a from IntervalIntegrable.refl)
    hmeas hc
  have hh := hd.const_add (P a x)
  apply hh.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
  have hv := spatialDerivative_increment_eq_parameter_integral F P D E l r a b x B
    ha hb hD hE hFt hFx hDx hEb
  linarith

end QuantitativeFollowup
