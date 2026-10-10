module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterSchemeStieltjes

@[expose] public section

/-! Honest Fubini against the literal finite free measure, proved by its
actual signed charges. The negative root charge is retained; integrability
is required only for the sample sections which are summed. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
set_option autoImplicit false
variable {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
set_option maxHeartbeats 1000000

theorem integral_cavityFiniteFree_swap (P : Measure Ω) (s : RSBScheme k)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (F : Ω→Paper.Overlap→ℝ)
    (hF : ∀r,Integrable (fun sample=>F sample r) P) :
    (∫sample,∫r,F sample r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a ∂P)=
      ∫r,∫sample,F sample r ∂P ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  have he (sample : Ω) :=
    (cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq (F sample)).symm
  simp_rw [he]
  rw [integral_finset_sum Finset.univ (fun i _=>
    (hF (cavityOuterSchemeChargeNode s i)).const_mul
      (cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) i))]
  simp_rw [integral_const_mul]
  exact cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq
    (fun r=>∫sample,F sample r ∂P)

theorem integrable_cavityFiniteFree_section (P : Measure Ω) (s : RSBScheme k)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (F : Ω→Paper.Overlap→ℝ)
    (hF : ∀r,Integrable (fun sample=>F sample r) P) :
    Integrable (fun sample=>∫r,F sample r
      ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) P :=by
  have he : (fun sample=>∫r,F sample r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)=
      fun sample=>∑i : Option (Option (Fin (k+1))),
        cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) i*
          F sample (cavityOuterSchemeChargeNode s i) :=
    funext fun sample=>(cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq (F sample)).symm
  rw [he]
  exact integrable_finset_sum Finset.univ fun i _=>
    (hF (cavityOuterSchemeChargeNode s i)).const_mul
      (cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) i)

end QuantitativeFollowup
