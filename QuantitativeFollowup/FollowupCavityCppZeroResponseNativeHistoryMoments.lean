module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeSchemeEnergyHistory
public import QuantitativeFollowup.FixedRowSymmetryPosteriorTransportHistory
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterMean

@[expose] public section

/-! Complete marked-history expectations transport from the actual outer
Gaussian posterior to the actual native finite-profile process. The
selected-node formula is a consequence of this whole-law identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem integral_cavityOuterPosteriorHistory_eq_native_scheme
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (F : (FiniteHistory (FiniteStateField (Configuration n)) (k+2)×Configuration n)→ℝ)
    (hF : Measurable F) :
    (∫p,F (cavityOuterHistoryMap (cavityFiniteEnergyInput D s) (k+2) (anisotropicRootEnergyMap D) 0 p)
      ∂cavityOuterPosteriorLaw (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) 0)=
    ∫p,F (cavitySchemeEnergyHistoryProjection D (cavityNativeSchemeHistory D s p.1),p.2)
      ∂anisotropicMeasureSpinPathLaw D (Paper.parisiSchemeMeasure s) a :=by
  have he:=congrArg (fun P : Measure (FiniteHistory (FiniteStateField (Configuration n)) (k+2)×Configuration n)=>
    ∫z,F z ∂P) (cavityOuterPosteriorHistory_eq_native_scheme D s a)
  have hm:Measurable (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>
      (cavitySchemeEnergyHistoryProjection D (cavityNativeSchemeHistory D s p.1),p.2)):=
    ((measurable_cavitySchemeEnergyHistoryProjection D).comp
      ((measurable_cavityNativeSchemeHistory D s).comp measurable_fst)).prodMk measurable_snd
  rw [integral_map (measurable_cavityOuterHistoryMap _ _ _ _).aemeasurable hF.aestronglyMeasurable,
    integral_map hm.aemeasurable hF.aestronglyMeasurable] at he
  exact he

theorem cavityOuterPosteriorMean_eq_native_scheme_node
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d≤k+2)
    (f : FiniteStateField (Configuration n)→ℝ) (hf : Measurable f) :
    cavityOuterPosteriorMean (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) f
      (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d) 0=
      ∫p,f (anisotropicEnergyMap D (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s (k+2-d) (by omega)) p.1))
        ∂anisotropicMeasureSpinPathLaw D (Paper.parisiSchemeMeasure s) a :=by
  let F:=fun p : FiniteHistory (FiniteStateField (Configuration n)) (k+2)×Configuration n=>
    f (p.1 ⟨k+2-d,by omega⟩)
  have hF:Measurable F:=hf.comp ((measurable_pi_apply _).comp measurable_fst)
  have he:=integral_cavityOuterPosteriorHistory_eq_native_scheme D s a F hF
  have ho(p):F (cavityOuterHistoryMap (cavityFiniteEnergyInput D s) (k+2) (anisotropicRootEnergyMap D) 0 p)=
      f (0+anisotropicRootEnergyMap D p.1+
        cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d p.2.1):=by
    dsimp only [F,cavityOuterHistoryMap]
    rw [cascadePosteriorHistory_eq_initial_add,cavityPosteriorLineFieldLinear_apply]
  simp_rw [ho] at he
  exact he

end QuantitativeFollowup
