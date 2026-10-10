module
public import QuantitativeFollowup.VectorConcentratingStieltjes
public import QuantitativeFollowup.ConcentratingDensity
public import QuantitativeFollowup.DeficitContactGeometry
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! Literal double integration by parts for the concentrating direction.
The second derivative is the actual a.e. derivative of the Lipschitz
increment; differentiability at its two corners is not required. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem contDiff_transportDeficit_one (S : ℝ → ℝ) (hS : Continuous S) :
    ContDiff ℝ 1 (transportDeficit S) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_transportDeficit S hS x).differentiableAt,?_⟩
  have he : deriv (transportDeficit S)=(fun x => x-S x) :=
    funext (fun x => (hasDerivAt_transportDeficit S hS x).deriv)
  rw [he]
  exact continuous_id.sub hS

theorem concentrating_deficit_second_pairing_unit (S D : ℝ → ℝ)
    (hS : Continuous S) (hD : Continuous D) (a ell : ℝ)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell)
    (hd : ∀x∈Icc a (a+ell), HasDerivAt S (D x) x) :
    (∫x in (0 : ℝ)..1, transportDeficit S x*deriv (concentratingIntervalIncrement a ell) x)=
      8*ell/15-concentratingDelta a ell D := by
  have hip := ((contDiff_transportDeficit_one S hS).contDiffOn.absolutelyContinuousOnInterval
      (a:=(0 : ℝ)) (b:=1)).integral_mul_deriv_eq_deriv_mul
    (concentratingIntervalIncrement_absoluteContinuous a ell 0 1 hell)
  have hz0 := concentratingIntervalIncrement_zero_outside a ell 0 hell
    (fun h => not_lt_of_ge ha.le h.1)
  have hz1 := concentratingIntervalIncrement_zero_outside a ell 1 hell
    (fun h => not_lt_of_ge he.le h.2)
  rw [hip,hz0,hz1,mul_zero,mul_zero,sub_zero,zero_sub]
  calc
    _ = ∫x in (0 : ℝ)..1, concentratingIntervalIncrement a ell x*(S x-x) := by
      rw [←intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [(hasDerivAt_transportDeficit S hS x).deriv]
      ring
    _ = _ := concentrating_pairing_unit S D hS hD a ell ha.le he.le hell hd

theorem vector_concentrating_deficit_second_pairing (μ : Paper.ParisiMeasure)
    (beta t outer : ℝ) (hbeta : beta ≠ 0) (ht : t < 1)
    (a ell : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) :
    (∫x in (0 : ℝ)..1, vectorOverlapDeficit (n:=n) μ beta t outer ht.le x*
      deriv (concentratingIntervalIncrement a ell) x)=
        8*ell/15-vectorConcentratingDelta (n:=n) μ beta t outer ht.le a ell := by
  apply concentrating_deficit_second_pairing_unit _ _
    (continuous_vectorMeanOverlapReal μ beta t outer ht.le)
    (continuous_vectorMeanOverlapDerivativeReal μ beta t outer ht.le) a ell ha he hell
  intro x hx
  exact hasDerivAt_vectorMeanOverlapReal μ beta t outer hbeta ht
    ⟨ha.trans_le hx.1,hx.2.trans_lt he⟩

end QuantitativeFollowup
