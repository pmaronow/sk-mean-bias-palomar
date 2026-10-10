module
public import QuantitativeFollowup.ScalarFiniteGaussianExpectation

@[expose] public section

/-! The actual squared-gradient diffusion moment is the normalized marked
Gaussian observable from the response calculation. No moment-law premise
is supplied; the retained-history equality and actual spin marginal prove it. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarFiniteObservationNode (s : RSBScheme k) (p : Fin (k+3)) : Paper.Overlap :=
  ⟨FRSB.forwardSchemeTime s 1 p,(FRSB.forwardSchemeTime s 1 p).coe_nonneg,
    FRSB.forwardSchemeTime_le s 1 p⟩

theorem scalarFiniteObservationNode_coe (s : RSBScheme k) (p : Fin (k+3)) :
    (scalarFiniteObservationNode s p:ℝ)=s.q p :=
  scalarSchemeHistoryClock_coe s p (by omega)

theorem scalarFiniteGradientSquare_selected (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (p : Fin (k+3)) (ω : Paper.BrownianSample) :
    scalarFiniteGradientSquare s β p (WithLp.toLp 2 (scalarSelectedHistory s β hβ ω))=
      FRSB.M β (Paper.parisiSchemeMeasure s) (scalarFiniteObservationNode s p) ω^2 := by
  have hs := parisiPhysicalSplitState_eq_selected β hβ (Paper.parisiSchemeMeasure s)
    (scalarFiniteObservationNode s p) ω
  simp only [scalarFiniteObservationNode,Real.toNNReal_coe] at hs
  change Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
    (FRSB.forwardSchemeTime s 1 p,
      Paper.selectedParisiItoState β 0 hβ (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p) ω)^2=_
  rw [←hs]
  exact congrArg (fun x:ℝ=>x^2) (scalarGradient_physicalSplitState β hβ
    (Paper.parisiSchemeMeasure s) (scalarFiniteObservationNode s p) ω)

/-- Literal Gaussian expectation for the constructed physical Γ, including
all retained repeated nodes and both endpoint observations. -/
theorem scalarFiniteGaussian_Gamma (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (p : Fin (k+3)) :
    FRSB.Gamma β (Paper.parisiSchemeMeasure s) (scalarFiniteObservationNode s p)=
      (1/2:ℝ)*∑e : Bool,∫z,Real.exp (scalarFiniteEuclideanExponent s β e
        (scalarFiniteGaussianInput s β z))*scalarFiniteGradientSquare s β p
          (scalarFiniteGaussianInput s β z) ∂fieldGaussian (k+2) := by
  let f : QuantitativePaper.Field (k+3)×Bool→ℝ := fun z=>scalarFiniteGradientSquare s β p z.1
  have hf : Measurable f := (contDiff_scalarFiniteGradientSquare s β p).continuous.measurable.comp measurable_fst
  have hg := integral_scalarGaussianMarkedLaw_euclidean_physical s β hβ f hf
  have hm : Measurable (fun ω=>FRSB.M β (Paper.parisiSchemeMeasure s)
      (scalarFiniteObservationNode s p) ω^2) :=
    (FRSB.measurable_M β (Paper.parisiSchemeMeasure s) _ (scalarFiniteObservationNode s p).property).pow_const 2
  have hp : (∫z,f (WithLp.toLp 2 (scalarSelectedHistory s β hβ z.1),z.2)
      ∂scalarMarkedSpinLaw β hβ (Paper.parisiSchemeMeasure s))=
      FRSB.Gamma β (Paper.parisiSchemeMeasure s) (scalarFiniteObservationNode s p) := by
    calc
      _ = ∫z,FRSB.M β (Paper.parisiSchemeMeasure s) (scalarFiniteObservationNode s p) z.1^2
          ∂scalarMarkedSpinLaw β hβ (Paper.parisiSchemeMeasure s) := by
        apply integral_congr_ae
        exact .of_forall fun z=>scalarFiniteGradientSquare_selected s β hβ p z.1
      _ = _ := integral_scalarMarkedSpinLaw_sample β hβ (Paper.parisiSchemeMeasure s) _ hm
  have he := integral_scalarGaussianMarkedLaw_euclidean s β hβ f hf 1
    (fun z=>norm_scalarFiniteGradientSquare_le_one s β p z.1)
  rw [hg,hp] at he
  exact he

end QuantitativeFollowup
