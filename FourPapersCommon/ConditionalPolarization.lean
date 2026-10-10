module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

@[expose] public section

/-! Conditional expectation commutes with the finite-basis polarization. -/
noncomputable section
open MeasureTheory
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω]

theorem condExp_polarization (P : Measure Ω) (m : MeasurableSpace Ω)
    (f g h : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P) (hh : Integrable h P) :
    P[(fun p => (f p-g p-h p)/2) | m] =ᵐ[P]
      fun p => ((P[f|m]) p-(P[g|m]) p-(P[h|m]) p)/2 := by
  have hs := condExp_smul (μ:=P) (1/2:ℝ) (f-g-h) m
  have h1 := condExp_sub (μ:=P) (hf.sub hg) hh m
  have h2 := condExp_sub (μ:=P) hf hg m
  have he : (fun p => (f p-g p-h p)/2) = (1/2:ℝ) • (f-g-h) := by
    funext p
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [he]
  filter_upwards [hs, h1, h2] with p hp h1p h2p
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hp h1p h2p
  rw [h1p, h2p] at hp
  exact hp.trans (by ring)

end FourPapersCommon
