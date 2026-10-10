module
public import FourPapersCommon.FiniteCascadeTreeReferenceCoordinates
public import FourPapersCommon.FiniteProductInterchange

@[expose] public section

/-! Exact reference-kernel pushforward of independent standard Gaussian
edge coordinates and independent terminal counting spins. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
attribute [local instance] isProbabilityMeasure_gaussianCoordinateLaw
  isFiniteMeasure_terminalSpinCountingLaw isFiniteKernel_finiteCascadeTreeReferenceKernel
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem finiteCascadeTreeReferenceKernel_eq_gaussian_coordinates
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S) :
    ((gaussianCoordinateLaw I T).prod (terminalSpinCountingLaw S T)).map
      (finiteCascadeTreeReferenceRecord L T H) = finiteCascadeTreeReferenceKernel L T H := by
  induction T generalizing H with
  | leaf =>
      change ((Measure.dirac ()).prod (Measure.count : Measure S)).map Prod.snd =
        Kernel.const _ Measure.count H
      rw [Kernel.const_apply, Measure.dirac_prod, Measure.map_map measurable_snd measurable_prodMk_left]
      exact Measure.map_id
  | @advance j T ih =>
      let shift : FiniteStateGaussianInput I → FiniteStateField S := fun z => H + L j z
      have hshift : Measurable shift := by dsimp [shift]; fun_prop
      have hrec : Measurable (fun p : FiniteStateGaussianInput I ×
          (GaussianCoordinates I T × TerminalSpins S T) =>
          (shift p.1,finiteCascadeTreeReferenceRecord L T (shift p.1) p.2)) :=
        (hshift.comp measurable_fst).prodMk
          ((measurable_finiteCascadeTreeReferenceRecord L T).comp
            ((hshift.comp measurable_fst).prodMk measurable_snd))
      have hassoc := Measure.prodAssoc_prod
        (μ:=stdGaussian (FiniteStateGaussianInput I))
        (ν:=gaussianCoordinateLaw I T) (τ:=terminalSpinCountingLaw S T)
      change (((stdGaussian _).prod (gaussianCoordinateLaw I T)).prod
          (terminalSpinCountingLaw S T)).map _ = _
      calc
        _ = ((stdGaussian (FiniteStateGaussianInput I)).prod
            ((gaussianCoordinateLaw I T).prod (terminalSpinCountingLaw S T))).map
            (fun p => (shift p.1,finiteCascadeTreeReferenceRecord L T (shift p.1) p.2)) := by
          rw [←hassoc,Measure.map_map hrec MeasurableEquiv.prodAssoc.measurable]
          rfl
        _ = _ := by
          ext s hs
          rw [Measure.map_apply hrec hs,Measure.prod_apply (hrec hs)]
          change _ = ((Kernel.id ×ₖ finiteCascadeTreeReferenceKernel L T) ∘ₖ
            finiteStateGaussianRawKernel (L j)) H s
          rw [Kernel.comp_apply' _ _ _ hs,finiteStateGaussianRawKernel_apply,
            lintegral_map (Kernel.measurable_coe _ hs) hshift]
          apply lintegral_congr
          intro z
          rw [Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod,
            Measure.map_apply measurable_prodMk_left hs,←ih (shift z),
            Measure.map_apply
              (show Measurable (finiteCascadeTreeReferenceRecord L T (shift z)) from
                (measurable_finiteCascadeTreeReferenceRecord L T).comp measurable_prodMk_left)
              (measurable_prodMk_left hs)]
          rfl
  | fork T U ihT ihU =>
      have hT : Measurable (finiteCascadeTreeReferenceRecord L T H) :=
        (measurable_finiteCascadeTreeReferenceRecord L T).comp
        (measurable_const.prodMk measurable_id)
      have hU : Measurable (finiteCascadeTreeReferenceRecord L U H) :=
        (measurable_finiteCascadeTreeReferenceRecord L U).comp
        (measurable_const.prodMk measurable_id)
      have hshuffle := map_product_interchange (gaussianCoordinateLaw I T)
        (gaussianCoordinateLaw I U) (terminalSpinCountingLaw S T) (terminalSpinCountingLaw S U)
      change (((gaussianCoordinateLaw I T).prod (gaussianCoordinateLaw I U)).prod
          ((terminalSpinCountingLaw S T).prod (terminalSpinCountingLaw S U))).map _ =
          (finiteCascadeTreeReferenceKernel L T ×ₖ finiteCascadeTreeReferenceKernel L U) H
      rw [Kernel.prod_apply,←ihT H,←ihU H,Measure.map_prod_map _ _ hT hU,
        ←hshuffle,Measure.map_map (hT.prodMap hU) (by fun_prop)]
      rfl

end FourPapersCommon
