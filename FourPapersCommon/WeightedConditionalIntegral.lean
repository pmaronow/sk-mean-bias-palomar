module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

/-! Genuine weighted conditional integrals and martingale cross terms.
Weights may depend on the whole known past. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω}

theorem integral_known_mul_condExp (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    [SigmaFinite (P.trim hm)] (Z F : Ω → ℝ) (hZ : StronglyMeasurable[m] Z)
    (hF : Integrable F P) (hZF : Integrable (fun x => Z x*F x) P) :
    (∫ x, Z x*P[F|m] x ∂P) = ∫ x, Z x*F x ∂P := by
  have hp := condExp_mul_of_stronglyMeasurable_left hZ hZF hF
  calc
    _ = ∫ x, P[Z*F|m] x ∂P := integral_congr_ae hp.symm
    _ = _ := integral_condExp hm

theorem integral_known_mul_martingale_cross {ι : Type*} [Preorder ι]
    {V : Filtration ι m₀} [SigmaFiniteFiltration P V]
    {M : ι → Ω → ℝ} (hM : Martingale M V P) {r q : ι} (hrq : r ≤ q)
    (Z : Ω → ℝ) (hZ : StronglyMeasurable[V r] Z)
    (hZq : Integrable (fun x => Z x*M q x) P) :
    (∫ x, Z x*M q x ∂P) = ∫ x, Z x*M r x ∂P := by
  have hp := integral_known_mul_condExp (V r) (V.le r) Z (M q) hZ (hM.integrable q) hZq
  calc
    _ = ∫ x, Z x*P[M q|V r] x ∂P := hp.symm
    _ = _ := integral_congr_ae ((hM.condExp_ae_eq hrq).mono fun x hx => by
      change Z x*P[M q|V r] x=Z x*M r x
      rw [hx])

end FourPapersCommon
