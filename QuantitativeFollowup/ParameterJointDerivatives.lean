module
public import QuantitativeFollowup.GaussianParameterResponse
public import Mathlib.Analysis.Calculus.FDeriv.Partial

@[expose] public section

/-! Genuine joint differentiability from continuous actual parameter and
spatial partial derivatives. This supplies the Gaussian response hypotheses
without replacing them by an assumed joint smoothness statement. -/
noncomputable section
open Set Filter
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasFDerivAt_joint_of_parameter_spatial_partials
    (F D : ℝ→E→ℝ) (L : ℝ→E→E→L[ℝ]ℝ) (S : Set ℝ)
    (hS : IsOpen S) (a : ℝ) (x : E) (ha : a∈S)
    (hFt : ∀u∈S,∀y,HasDerivAt (fun v=>F v y) (D u y) u)
    (hFx : ∀u∈S,∀y,HasFDerivAt (F u) (L u y) y)
    (hD : ContinuousOn (Function.uncurry D) (S×ˢuniv))
    (hL : ContinuousOn (Function.uncurry L) (S×ˢuniv)) :
    HasFDerivAt (Function.uncurry F)
      ((ContinuousLinearMap.toSpanSingleton ℝ (D a x)).coprod (L a x)) (a,x) := by
  have hp : (a,x)∈S×ˢ(univ : Set E) := ⟨ha,mem_univ x⟩
  have hn : ∀ᶠp : ℝ×E in 𝓝 (a,x),p.1∈S := by
    filter_upwards [(hS.prod isOpen_univ).mem_nhds hp] with p hp
    exact hp.1
  have h1 : ∀ᶠp : ℝ×E in 𝓝 (a,x),
      HasFDerivAt (fun u=>F u p.2) (ContinuousLinearMap.toSpanSingleton ℝ (D p.1 p.2)) p.1 := by
    filter_upwards [hn] with p hp
    exact (hFt p.1 hp p.2).hasFDerivAt
  have h2 : ∀ᶠp : ℝ×E in 𝓝 (a,x),HasFDerivAt (F p.1) (L p.1 p.2) p.2 := by
    filter_upwards [hn] with p hp
    exact hFx p.1 hp p.2
  have hcD : ContinuousAt (fun p : ℝ×E=>ContinuousLinearMap.toSpanSingleton ℝ (D p.1 p.2)) (a,x) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp
      (hD.continuousAt ((hS.prod isOpen_univ).mem_nhds hp))
  exact (hasStrictFDerivAt_uncurry_coprod (f := F)
    (f₁ := fun u y=>ContinuousLinearMap.toSpanSingleton ℝ (D u y))
    (f₂ := L) h1 h2 hcD (hL.continuousAt ((hS.prod isOpen_univ).mem_nhds hp))).hasFDerivAt

theorem gaussianParameterDerivative_eq_actual_partial {m : ℕ}
    (F D : ℝ→QuantitativePaper.Field m→ℝ)
    (L : ℝ→QuantitativePaper.Field m→QuantitativePaper.Field m→L[ℝ]ℝ) (S : Set ℝ)
    (hS : IsOpen S) (a : ℝ) (x : QuantitativePaper.Field m) (ha : a∈S)
    (hFt : ∀u∈S,∀y,HasDerivAt (fun v=>F v y) (D u y) u)
    (hFx : ∀u∈S,∀y,HasFDerivAt (F u) (L u y) y)
    (hD : ContinuousOn (Function.uncurry D) (S×ˢuniv))
    (hL : ContinuousOn (Function.uncurry L) (S×ˢuniv)) :
    gaussianParameterDerivative F a x=D a x := by
  have hd := hasFDerivAt_joint_of_parameter_spatial_partials F D L S hS a x ha hFt hFx hD hL
  rw [gaussianParameterDerivative,hd.fderiv]
  simp only [ContinuousLinearMap.coprod_apply,ContinuousLinearMap.toSpanSingleton_apply,
    map_zero,smul_eq_mul,one_mul,add_zero]

end QuantitativeFollowup
