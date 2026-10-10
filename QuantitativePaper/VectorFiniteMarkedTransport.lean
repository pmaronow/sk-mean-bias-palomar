module
public import QuantitativePaper.VectorFiniteSpinPathLaw
public import QuantitativePaper.VectorOverlapScore
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-! The constructed finite diffusion/spin law and the Gaussian-coordinate
posterior have the identical retained-history expectations and variances.
This uses their proved pushforward laws and allows arbitrary measurable
history observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}

theorem integral_vectorFiniteSpinPathLaw_history (s : RSBScheme k) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1)
    (F : FiniteHistory (VectorState n) (k+2)×Configuration n→ℝ) (hF : Measurable F) :
    (∫p,F (vectorFiniteHistory s β t ht.le (k+2) p.1,p.2)
      ∂vectorFiniteSpinPathLaw s β t a ht.le)=
      ∫p,F p ∂vectorJointLaw s β t a := by
  rw [←vectorFiniteSpinPathLaw_map s β t a hβ ht]
  exact (integral_map
    ((measurable_vectorFiniteHistory s β t ht.le _).comp measurable_fst |>.prodMk
      measurable_snd).aemeasurable hF.aestronglyMeasurable).symm

theorem integral_vectorEuclideanJointLaw_history (s : RSBScheme k) (β t a : ℝ)
    (F : FiniteHistory (VectorState n) (k+2)×Configuration n→ℝ) (hF : Measurable F) :
    (∫p,F (vectorEuclideanJointMap s β t p) ∂vectorEuclideanJointLaw s β t a)=
      ∫p,F p ∂vectorJointLaw s β t a := by
  rw [←vectorEuclideanJointLaw_map s β t a]
  exact (integral_map (measurable_vectorEuclideanJointMap s β t).aemeasurable
    hF.aestronglyMeasurable).symm

theorem variance_vectorFiniteSpinPathLaw_history (s : RSBScheme k) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1)
    (F : FiniteHistory (VectorState n) (k+2)×Configuration n→ℝ) (hF : Measurable F) :
    variance (fun p=>F (vectorFiniteHistory s β t ht.le (k+2) p.1,p.2))
      (vectorFiniteSpinPathLaw s β t a ht.le)=variance F (vectorJointLaw s β t a) := by
  rw [←vectorFiniteSpinPathLaw_map s β t a hβ ht]
  exact (variance_map hF.aemeasurable
    ((measurable_vectorFiniteHistory s β t ht.le _).comp measurable_fst |>.prodMk
      measurable_snd).aemeasurable).symm

theorem variance_vectorEuclideanJointLaw_history (s : RSBScheme k) (β t a : ℝ)
    (F : FiniteHistory (VectorState n) (k+2)×Configuration n→ℝ) (hF : Measurable F) :
    variance (fun p=>F (vectorEuclideanJointMap s β t p))
      (vectorEuclideanJointLaw s β t a)=variance F (vectorJointLaw s β t a) := by
  rw [←vectorEuclideanJointLaw_map s β t a]
  exact (variance_map hF.aemeasurable
    (measurable_vectorEuclideanJointMap s β t).aemeasurable).symm

end QuantitativePaper
