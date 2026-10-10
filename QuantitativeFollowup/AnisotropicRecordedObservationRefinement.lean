module
public import QuantitativeFollowup.AnisotropicObservationSemigroup
public import FourPapersCommon.FiniteObservationTreeRefinement

@[expose] public section

/-! An actual observation subdivision changes no retained genealogical law.
Every original field/spin is recovered by the explicit projection. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem anisotropicRecordedProfileTreeKernel_block_collapse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (Q : ℕ→Paper.Overlap) (hQ : Antitone Q)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (d : ℕ) :
    (anisotropicRecordedProfileTreeKernel D μ Q (.advance (observationTreePad T d))).map
      (observationBlockCollapse T d)=
      (Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ Q T) ∘ₖ
        anisotropicObservationTransition D μ (Q (j+d+1)) (Q j) := by
  induction d with
  | zero =>
      change ((_ ×ₖ _) ∘ₖ _).map id=_
      rw [Kernel.map_id]
      rfl
  | succ d ih =>
      change ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ Q
          (.advance (observationTreePad T d))) ∘ₖ
        anisotropicObservationTransition D μ (Q (j+d+1+1)) (Q (j+d+1))).map
          (observationBlockCollapse T d ∘ Prod.snd)=_
      rw [Kernel.map_comp,Kernel.map_comp_right _ measurable_snd (measurable_observationBlockCollapse T d),
        ←Kernel.snd_eq,Kernel.snd_prod,ih,Kernel.comp_assoc,
        anisotropicObservationTransition_semigroup D μ (Q (j+d+1+1)) (Q (j+d+1)) (Q j)
          (hQ (by omega)) (hQ (by omega))]
      simp only [Nat.add_assoc]

theorem anisotropicRecordedProfileTreeKernel_refinement (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q Q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hQ : Antitone Q) (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (anisotropicRecordedProfileTreeKernel D μ Q (observationRefineTree d T)).map
      (observationRefinementProject d T)=anisotropicRecordedProfileTreeKernel D μ q T := by
  induction T with
  | leaf => exact Kernel.map_id _
  | @advance j T ih =>
      change (anisotropicRecordedProfileTreeKernel D μ Q
        (.advance (observationTreePad (observationRefineTree d T) (d j)))).map
        ((Prod.map id (observationRefinementProject d T)) ∘
          observationBlockCollapse (observationRefineTree d T) (d j))=_
      rw [Kernel.map_comp_right _ (measurable_observationBlockCollapse _ _)
          (measurable_id.prodMap (measurable_observationRefinementProject d T)),
        anisotropicRecordedProfileTreeKernel_block_collapse D μ Q hQ,
        Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
          (measurable_observationRefinementProject d T),Kernel.map_id,ih]
      have he : observationRefinementDepth d j+d j+1=observationRefinementDepth d (j+1):=rfl
      rw [he,hlevels j,hlevels (j+1)]
  | fork T U ihT ihU =>
      change (_ ×ₖ _).map (Prod.map _ _)=_
      rw [←Kernel.map_prod_map _ _ (measurable_observationRefinementProject d T)
        (measurable_observationRefinementProject d U),ihT,ihU]

theorem anisotropicRecordedProfileTreeLaw_refinement (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q Q : ℕ→Paper.Overlap) (d : ℕ→ℕ)
    (hQ : Antitone Q) (hlevels : ∀j,Q (observationRefinementDepth d j)=q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T)).map
      (Prod.map id (observationRefinementProject d T))=anisotropicRecordedProfileTreeLaw D μ a q T := by
  rw [anisotropicRecordedProfileTreeLaw,anisotropicRecordedProfileTreeLaw,
    ←Measure.compProd_map (measurable_observationRefinementProject d T),
    anisotropicRecordedProfileTreeKernel_refinement D μ q Q d hQ hlevels]

end QuantitativeFollowup
