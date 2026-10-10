module
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-! Differentiation of an attained stationary Legendre value. The derivative
of the selected inverse field cancels against the actual spatial derivative. -/
noncomputable section
open scoped InnerProductSpace
namespace FourPapersCommon
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasFDerivAt_stationaryLegendre_value (U : A×E→ℝ) (Y : A→E)
    (a : A) (m : E) (DU : A×E→L[ℝ]ℝ) (DY : A→L[ℝ]E)
    (hU : HasFDerivAt U DU (a,Y a)) (hY : HasFDerivAt Y DY a)
    (hstationary : ∀w : E,DU (0,w)=inner ℝ m w) :
    HasFDerivAt (fun p=>inner ℝ m (Y p)-U (p,Y p))
      (-(DU.comp (ContinuousLinearMap.inl ℝ A E))) a := by
  have hdInner:=((innerSL ℝ m).hasFDerivAt).comp a hY
  have hdU:=hU.comp a ((hasFDerivAt_id a).prodMk hY)
  convert hdInner.sub hdU using 1
  · funext v
    rfl
  · ext v
    change -DU (v,0)=inner ℝ m (DY v)-DU (v,DY v)
    have hs : DU (v,DY v)=DU (v,0)+DU (0,DY v) := by
      rw [←map_add]
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    rw [hs,hstationary]
    ring

end FourPapersCommon
