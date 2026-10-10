module
public import QuantitativePaper.ResponseTentFunctionals
public import QuantitativePaper.ResponseCurvatureProposition

@[expose] public section

/-! Literal quantitative-manuscript Appendix A.2 target. Profiles are actual
probability measures; admissibility means the stated energy-scale root floor.
All response expectations and the Stieltjes measure are constructed objects. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper

def ResponseMidpointTarget : Prop :=
  ∀(n : ℕ),0<n→∀(β t lam : ℝ)(hβ : 0<β)(ht : t∈Ico (0:ℝ) 1),
    lam∈Icc (0:ℝ) β→∀μ ν : Paper.ParisiMeasure,
      lam≤β*Paper.parisiCDF μ 0→lam≤β*Paper.parisiCDF ν 0→
    ConvexOn ℝ (Icc (0:ℝ) 1)
      (fun θ=>responseEnergyFunctional n (Paper.parisiMix μ ν θ) β t lam) ∧
    (1≤β→∀(ell κ U bbar Sigma : ℝ),ell∈Ioc (0:ℝ) 1→0<κ→0≤U→0<bbar→0≤Sigma→
      (∀θ∈Ioo (0:ℝ) 1,∀q∈Icc (ell/4) (3*ell/4),
        κ≤β*(Paper.parisiCDF ν q-Paper.parisiCDF μ q))→
      (∀θ∈Ioo (0:ℝ) 1,∀q∈Icc (ell/4) (3*ell/4),
        β*Paper.parisiCDF (Paper.parisiMix μ ν θ) q≤U)→
      (∀θ∈Ioo (0:ℝ) 1,∀q∈Icc (ell/4) (3*ell/4),
        responseMeanHessianReal (n:=n) (Paper.parisiMix μ ν θ) β t lam ht.2.le q≤bbar)→
      (∀θ∈Ioo (0:ℝ) 1,(1-t)*β*
        (∫q : Paper.Overlap in {q : Paper.Overlap | (q:ℝ)∈Icc (ell/4) (3*ell/4)},
          responseAveragedCurvature (n:=n) (Paper.parisiMix μ ν θ) β t lam ht.2.le q
          ∂(Paper.parisiMix μ ν θ : Measure Paper.Overlap))≤Sigma)→
      (responseCurvatureConstant U)^4*(1-t)^3*κ^2*ell^3/
        (128*(8*bbar+ell*Sigma))≤
          responseEnergyFunctional n μ β t lam+responseEnergyFunctional n ν β t lam-
            2*responseEnergyFunctional n (Paper.parisiMix μ ν (1/2)) β t lam)

end QuantitativePaper
