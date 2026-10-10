module
public import Mathlib.Probability.ProductMeasure

@[expose] public section

/-! Swapping two finite independent-coordinate indices preserves the actual
product probability law. This also covers empty coordinate sets. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon

theorem finiteProductTranspose_map {I J A : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace A] (P : I → J → Measure A)
    [∀ i j, IsProbabilityMeasure (P i j)] :
    (Measure.pi (fun i => Measure.pi (P i))).map (fun z j i => z i j) =
      Measure.pi (fun j => Measure.pi (fun i => P i j)) := by
  let U : (I → J → A) → (I × J → A) := (MeasurableEquiv.curry I J A).symm
  let S : (I × J → A) → (J × I → A) :=
    MeasurableEquiv.piCongrLeft (fun _ => A) (Equiv.prodComm I J)
  let C : (J × I → A) → (J → I → A) := MeasurableEquiv.curry J I A
  have hU : Measurable U := (MeasurableEquiv.curry I J A).symm.measurable
  have hS : Measurable S := (MeasurableEquiv.piCongrLeft (fun _ => A)
    (Equiv.prodComm I J)).measurable
  have hC : Measurable C := (MeasurableEquiv.curry J I A).measurable
  have hmap : (fun z : I → J → A => fun j i => z i j) = C ∘ S ∘ U := rfl
  rw [hmap, ← Function.comp_assoc, ← Measure.map_map (hC.comp hS) hU,
    ← Measure.map_map hC hS]
  have hu := Measure.infinitePi_map_curry_symm P
  simp only [Measure.infinitePi_eq_pi] at hu
  rw [show U = (MeasurableEquiv.curry I J A).symm from rfl, hu]
  have hs := Measure.pi_map_piCongrLeft (Equiv.prodComm I J)
    (fun p : J × I => P p.2 p.1)
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] at hs
  rw [show S = MeasurableEquiv.piCongrLeft (fun _ => A) (Equiv.prodComm I J) from rfl, hs]
  have hc := Measure.infinitePi_map_curry (fun j i => P i j)
  simp only [Measure.infinitePi_eq_pi] at hc
  exact hc

end FourPapersCommon
