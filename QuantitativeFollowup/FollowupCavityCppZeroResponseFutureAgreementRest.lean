module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFutureAgreementTransition
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowSecondSpatialSmooth

@[expose] public section

/-! True pointwise agreement of the finite rest-square average with the
native restarted future self-overlap, and equality of their field derivatives.
The finite parameter is the physical disorder/field point, not whitened noise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFiniteRowFutureRestSquare_eq_native (s : RSBScheme k) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (p j : ℕ)
    (hp : p≤j) (hj : j≤k+2) (g : AnisotropicDisorder n) (x : Field n) (i : Fin n) :
    cavityFiniteRowFutureRestSquare s n β ρ hβ hρ p (j-p) i
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x)=
      anisotropicRestartSpinSquare (followupCavityRestSpinModel n β ρ hβ hρ)
        (Paper.parisiSchemeMeasure s) g (anisotropicFiniteMeshNode s (k+2-j)) x i
        (anisotropicFiniteMeshNode s (k+2-p)) :=
  cavityFutureAgreement_finite_coordinate_square _ s p j hp hj g x i

theorem cavityFiniteRowFutureRestSquare_average_eq_native (s : RSBScheme k) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (p j : ℕ)
    (hp : p≤j) (hj : j≤k+2) (g : AnisotropicDisorder n) (x : Field n) :
    (∑i : Fin n,cavityFiniteRowFutureRestSquare s n β ρ hβ hρ p (j-p) i
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x))/(n:ℝ)=
      anisotropicRestartMeanSquare (followupCavityRestSpinModel n β ρ hβ hρ)
        (Paper.parisiSchemeMeasure s) g (anisotropicFiniteMeshNode s (k+2-j)) x
        (anisotropicFiniteMeshNode s (k+2-p)) := by
  simp only [cavityFiniteRowFutureRestSquare_eq_native s β ρ hβ hρ p j hp hj g x,
    anisotropicRestartMeanSquare]

theorem fderiv_cavityFiniteRowFutureRestSquare_average_eq_native (s : RSBScheme k) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (p j : ℕ)
    (hp : p≤j) (hj : j≤k+2) (g : AnisotropicDisorder n) (x : Field n) :
    fderiv ℝ (fun y=>(∑i : Fin n,cavityFiniteRowFutureRestSquare s n β ρ hβ hρ p (j-p) i
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n y))/(n:ℝ)) x=
    fderiv ℝ (fun y=>anisotropicRestartMeanSquare (followupCavityRestSpinModel n β ρ hβ hρ)
      (Paper.parisiSchemeMeasure s) g (anisotropicFiniteMeshNode s (k+2-j)) y
      (anisotropicFiniteMeshNode s (k+2-p))) x := by
  have he:=funext (cavityFiniteRowFutureRestSquare_average_eq_native s β ρ hβ hρ p j hp hj g)
  rw [he]

theorem cavityFiniteRowFutureRestSquare_average_smooth (s : RSBScheme k) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (p j : ℕ)
    (g : AnisotropicDisorder n) :
    ContDiff ℝ ∞ (fun x=>(∑i : Fin n,cavityFiniteRowFutureRestSquare s n β ρ hβ hρ p j i
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x))/(n:ℝ)) := by
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i _
  exact (contDiff_cavityFiniteRowFutureRestSquare s n β ρ hβ hρ p j i).comp
    (contDiff_const.add (anisotropicFieldInjection n).contDiff)

theorem contDiff_cavityFutureAgreement_native_meanSquare (s : RSBScheme k) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (p j : ℕ)
    (hp : p≤j) (hj : j≤k+2) (g : AnisotropicDisorder n) :
    ContDiff ℝ ∞ (fun x=>anisotropicRestartMeanSquare (followupCavityRestSpinModel n β ρ hβ hρ)
      (Paper.parisiSchemeMeasure s) g (anisotropicFiniteMeshNode s (k+2-j)) x
      (anisotropicFiniteMeshNode s (k+2-p))) := by
  have he:=funext (cavityFiniteRowFutureRestSquare_average_eq_native s β ρ hβ hρ p j hp hj g)
  rw [←he]
  exact cavityFiniteRowFutureRestSquare_average_smooth s β ρ hβ hρ p (j-p) g

theorem hasFDerivAt_cavityFiniteRowFutureRestSquare_average_native (s : RSBScheme k) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (p j : ℕ)
    (hp : p≤j) (hj : j≤k+2) (g : AnisotropicDisorder n) (x : Field n) :
    HasFDerivAt (fun y=>(∑i : Fin n,cavityFiniteRowFutureRestSquare s n β ρ hβ hρ p (j-p) i
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n y))/(n:ℝ))
      (fderiv ℝ (fun y=>anisotropicRestartMeanSquare (followupCavityRestSpinModel n β ρ hβ hρ)
        (Paper.parisiSchemeMeasure s) g (anisotropicFiniteMeshNode s (k+2-j)) y
        (anisotropicFiniteMeshNode s (k+2-p))) x) x := by
  have hd:=((cavityFiniteRowFutureRestSquare_average_smooth s β ρ hβ hρ p (j-p) g).differentiable
    (by simp) x).hasFDerivAt
  rw [fderiv_cavityFiniteRowFutureRestSquare_average_eq_native s β ρ hβ hρ p j hp hj g x] at hd
  exact hd

end QuantitativeFollowup
