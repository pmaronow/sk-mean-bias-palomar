module
public import QuantitativePaper.VectorProfileOuterFunctional
public import QuantitativePaper.VectorGridProfileMix
public import QuantitativePaper.VectorDyadicGridAgreement
public import QuantitativePaper.ResponseFunctional

@[expose] public section

/-! The finite profile functional is literally the physical measure
functional of the common dyadic mixture, including its zero-tilt branch. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorProfile_grid_functional_eq (μ ν : Paper.ParisiMeasure) (j : ℕ)
    (β t lam θ : ℝ) (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1) :
    vectorProfileFiniteEnergyFunctional (n:=n)
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t lam θ=
      responseEnergyFunctional n
        (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t lam:=by
  have hpot : (fun p : Couplings n×ℝ=>vectorProfileRecursion
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t θ p
        (vectorDyadicIndex j+3) 0)=
      (fun p=>vectorMeasurePotential
        (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t p 0):=by
    funext p
    rw [vectorProfileRecursion_eq_scheme _ _ β t θ hθ,
      vector_grid_profile_scheme_eq_mix μ ν (vectorDyadicIndex j) θ hθ,
      vectorMeasurePotential_grid_eq_finite (Paper.parisiMix μ ν θ) j β t ht p]
  unfold vectorProfileFiniteEnergyFunctional vectorProfileOuterEnergy
    vectorProfileOuterNormalized responseEnergyFunctional vectorMeasureFunctional
  rw [hpot,FRSB.parisiSchemeMeasure_grid_eq,FRSB.parisiSchemeMeasure_grid_eq,
    ←parisiGridMeasure_mix μ ν (vectorDyadicIndex j) θ hθ]
  rw [sub_div,div_div]
  congr 1
  by_cases hβ : β=0
  · simp [hβ]
  · field_simp [hβ]
    <;>ring

end QuantitativePaper
