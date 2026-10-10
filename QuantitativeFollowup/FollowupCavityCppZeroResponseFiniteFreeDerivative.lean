module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterSchemeStieltjes
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Differentiation against the actual finite free overlap measure.
The genuine signed charge formula includes the negative outer root charge;
derivatives follow from a finite sum, without a passage under a Gaussian or
Lebesgue integral. Repeated overlap atoms are retained. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
set_option autoImplicit false
variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1000000

theorem hasFDerivAt_cavityFiniteFreeIntegral (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (F : E→Paper.Overlap→ℝ) (D : Paper.Overlap→E→L[ℝ]ℝ) (x : E)
    (hF : ∀q,HasFDerivAt (fun y=>F y q) (D q) x) :
    HasFDerivAt (fun y=>∫q,F y q ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)
      (∑i : Option (Option (Fin (k+1))),
        cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) i •
          D (cavityOuterSchemeChargeNode s i)) x :=by
  have he : (fun y=>∫q,F y q ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)=
      (fun y=>∑i : Option (Option (Fin (k+1))),
        cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) i*
          F y (cavityOuterSchemeChargeNode s i)) :=
    funext fun y=>(cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq (F y)).symm
  rw [he]
  exact HasFDerivAt.fun_sum fun i _=>(hF (cavityOuterSchemeChargeNode s i)).const_mul _

theorem fderiv_cavityFiniteFreeIntegral_apply_of_hasFDerivAt (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (F : E→Paper.Overlap→ℝ) (D : Paper.Overlap→E→L[ℝ]ℝ) (x : E)
    (hF : ∀q,HasFDerivAt (fun y=>F y q) (D q) x) (v : E) :
    fderiv ℝ (fun y=>∫q,F y q ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) x v=
      ∫q,D q v ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  rw [(hasFDerivAt_cavityFiniteFreeIntegral s a ha has hq F D x hF).fderiv]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  exact cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq (fun q=>D q v)

theorem fderiv_cavityFiniteFreeIntegral_apply (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (F : E→Paper.Overlap→ℝ) (x : E)
    (hF : ∀q,DifferentiableAt ℝ (fun y=>F y q) x) (v : E) :
    fderiv ℝ (fun y=>∫q,F y q ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) x v=
      ∫q,fderiv ℝ (fun y=>F y q) x v ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=
  fderiv_cavityFiniteFreeIntegral_apply_of_hasFDerivAt s a ha has hq F _ x
    (fun q=>(hF q).hasFDerivAt) v

theorem contDiff_cavityFiniteFreeIntegral (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0) (N : ℕ∞ω)
    (F : E→Paper.Overlap→ℝ) (hF : ∀q,ContDiff ℝ N (fun y=>F y q)) :
    ContDiff ℝ N (fun y=>∫q,F y q ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) :=by
  have he : (fun y=>∫q,F y q ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)=
      (fun y=>∑i : Option (Option (Fin (k+1))),
        cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) i*
          F y (cavityOuterSchemeChargeNode s i)) :=
    funext fun y=>(cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq (F y)).symm
  rw [he]
  exact ContDiff.sum fun i _=>contDiff_const.mul (hF (cavityOuterSchemeChargeNode s i))

end QuantitativeFollowup
