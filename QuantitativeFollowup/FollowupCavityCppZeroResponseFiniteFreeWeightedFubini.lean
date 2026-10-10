module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeFubini

@[expose] public section

/-! Weighted sample/free-measure Fubini for the literal finite profile.
The finite signed-charge representation proves the interchange, including
the negative outer root charge. No joint integrability is presumed. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
set_option autoImplicit false

theorem integral_cavityFiniteFree_weighted_swap (P : Measure Ω) (s : RSBScheme k)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (W : Ω→ℝ) (F : Ω→Paper.Overlap→ℝ)
    (hF : ∀r,Integrable (fun sample=>W sample*F sample r) P) :
    (∫sample,W sample*(∫r,F sample r
      ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) ∂P)=
      ∫r,∫sample,W sample*F sample r ∂P
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  have he (sample : Ω) : W sample*(∫r,F sample r
      ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)=
      ∫r,W sample*F sample r
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=
    (integral_const_mul _ _).symm
  simp_rw [he]
  exact integral_cavityFiniteFree_swap P s a ha has hq
    (fun sample r=>W sample*F sample r) hF

theorem integrable_cavityFiniteFree_weighted_section (P : Measure Ω) (s : RSBScheme k)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (W : Ω→ℝ) (F : Ω→Paper.Overlap→ℝ)
    (hF : ∀r,Integrable (fun sample=>W sample*F sample r) P) :
    Integrable (fun sample=>W sample*(∫r,F sample r
      ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)) P :=by
  have he : (fun sample=>W sample*(∫r,F sample r
      ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))=
      fun sample=>∫r,W sample*F sample r
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
    funext sample
    exact (integral_const_mul _ _).symm
  rw [he]
  exact integrable_cavityFiniteFree_section P s a ha has hq
    (fun sample r=>W sample*F sample r) hF

theorem integral_cavityFiniteFree_double_swap (P : Measure Ω) (s : RSBScheme k)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (F : Ω→Paper.Overlap→Paper.Overlap→ℝ)
    (hF : ∀r l,Integrable (fun sample=>F sample r l) P) :
    (∫sample,∫r,∫l,F sample r l
      ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
      ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a ∂P)=
      ∫r,∫l,∫sample,F sample r l ∂P
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  rw [integral_cavityFiniteFree_swap P s a ha has hq
    (fun sample r=>∫l,F sample r l
      ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)
    (fun r=>integrable_cavityFiniteFree_section P s a ha has hq
      (fun sample l=>F sample r l) (hF r))]
  apply integral_congr_ae
  exact .of_forall fun r=>integral_cavityFiniteFree_swap P s a ha has hq
    (fun sample l=>F sample r l) (hF r)

end QuantitativeFollowup
