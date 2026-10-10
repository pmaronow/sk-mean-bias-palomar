module
public import QuantitativeFollowup.ConcentratingPairing
public import QuantitativePaper.VectorMeanOverlapDifferentiation

@[expose] public section

/-! The concentrating curvature mass for the actual vector diffusion.
All derivative and response bounds come from the constructed state and the
proved all-profile Hessian-energy evolution. -/
noncomputable section
open Set MeasureTheory QuantitativePaper FourPapersCommon
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
variable {n : ℕ}

def vectorConcentratingDelta (μ : Paper.ParisiMeasure) (beta t outer : ℝ) (ht : t ≤ 1)
    (a ell : ℝ) : ℝ :=
  concentratingDelta a ell (fun x => vectorMeanOverlapDerivative (n:=n) μ beta t outer ht
    (projIcc (0 : ℝ) 1 zero_le_one x))

theorem vector_concentrating_pairing (μ : Paper.ParisiMeasure) (beta t outer : ℝ)
    (hbeta : beta ≠ 0) (ht : t < 1) (a ell : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) :
    (∫x in (0 : ℝ)..1, concentratingIntervalIncrement a ell x *
      (vectorMeanOverlapReal (n:=n) μ beta t outer ht.le x-x)) =
        8*ell/15-vectorConcentratingDelta (n:=n) μ beta t outer ht.le a ell := by
  apply concentrating_pairing_unit _ _
    (continuous_vectorMeanOverlapReal μ beta t outer ht.le)
    (continuous_vectorMeanOverlapDerivativeReal μ beta t outer ht.le) a ell ha.le he.le hell
  intro x hx
  exact hasDerivAt_vectorMeanOverlapReal μ beta t outer hbeta ht
    ⟨ha.trans_le hx.1, hx.2.trans_lt he⟩

theorem vectorConcentratingDelta_bounds (μ : Paper.ParisiMeasure) (beta t outer : ℝ)
    (hbeta : beta ≠ 0) (ht : t < 1) (a ell : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) :
    0 ≤ vectorConcentratingDelta (n:=n) μ beta t outer ht.le a ell ∧
      vectorConcentratingDelta (n:=n) μ beta t outer ht.le a ell ≤
        vectorMeanOverlapReal (n:=n) μ beta t outer ht.le (a+ell)-
          vectorMeanOverlapReal (n:=n) μ beta t outer ht.le a := by
  apply concentratingDelta_nonneg_le_increment _ _
    (continuous_vectorMeanOverlapDerivativeReal μ beta t outer ht.le)
    (fun x => vectorMeanOverlapDerivative_nonneg μ beta t outer ht.le _) a ell hell
  intro x hx
  exact hasDerivAt_vectorMeanOverlapReal μ beta t outer hbeta ht
    ⟨ha.trans_le hx.1, hx.2.trans_lt he⟩

theorem vectorConcentratingDelta_mem_unit (μ : Paper.ParisiMeasure) (beta t outer : ℝ)
    (hbeta : beta ≠ 0) (ht : t < 1) (a ell : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) :
    vectorConcentratingDelta (n:=n) μ beta t outer ht.le a ell ∈ Icc (0 : ℝ) 1 := by
  have hb := vectorConcentratingDelta_bounds (n:=n) μ beta t outer hbeta ht a ell ha he hell
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hl := (vectorMeanOverlapReal_nonneg_le_one (n:=n) μ beta t outer ht.le a).1
  have hu := (vectorMeanOverlapReal_nonneg_le_one (n:=n) μ beta t outer ht.le (a+ell)).2
  linarith

end QuantitativeFollowup
